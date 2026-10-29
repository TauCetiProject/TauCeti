/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.GraphStep.Basic

/-!
# The bounded first-order trajectory operator

The operator `D_A = d/ds + A(s)` acts from the first-order weak-derivative graph to `Lᵖ`
for any essentially bounded, strongly measurable family of bounded operators on a real Banach
space. We use the existing `WeakDerivStep` over the identity map on `Lᵖ`, so its norm controls
both the value and its weak derivative. No new Sobolev carrier is introduced.

`WeakDerivStep.trajectoryOperator` is a continuous linear map. Its operator norm is at most
`1 + ‖A‖`, and changing the coefficient changes the operator by at most the `L∞` distance
between coefficients. Solving `D_A u = f` is equivalent to the weak ordinary differential
equation `u' = f - A u`. For differentiable representatives with locally integrable derivative,
the operator agrees almost everywhere with the classical expression `u' + A u`.

These statements supply the bounded realization to which coercive estimates and compact-error
criteria can be applied. They do not assert Fredholmness, asymptotic invertibility, or density
of smooth paths. Neither symmetry nor finite dimensionality of the target is required.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.1 (first-order Fredholm operators).
* M. Schwarz, *Morse Homology*, Chapter 2 (linearized trajectory operators).

The coefficient action is Mathlib's `ContinuousLinearMap.holderL`, applied to evaluation;
the domain is the closed weak-derivative graph of `TauCeti.Analysis.Sobolev.GraphStep.Basic`.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ}
  {p : ENNReal} [Fact (1 ≤ p)]

/-- The first-order operator `u ↦ u' + A u` on the weak-derivative graph over `Lᵖ`.
The coefficient is an `L∞` operator field, so the definition depends only on its almost
everywhere equivalence class. -/
def trajectoryOperator (A : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))
      →L[ℝ] Lp F p (mu.restrict Omega) :=
  ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLpL p (mu.restrict Omega)).comp
      (weakFDerivL (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) +
    ((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holderL (mu.restrict Omega) ∞ p p A).comp
      (prevL (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))))

/-- The operator is the sum of the weak derivative in direction `1` and the coefficient action. -/
@[simp]
lemma trajectoryOperator_apply (A : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    trajectoryOperator A u =
      (ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLp
        (weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u) +
      (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p A
        (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u) := by
  simp [trajectoryOperator]
  -- Mathlib's `compLpL` has no application equality lemma, only an a.e. formula.
  rfl

/-- On representatives, the bounded trajectory operator has the expected pointwise formula
almost everywhere. -/
theorem trajectoryOperator_apply_ae (A : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) :
    trajectoryOperator A u =ᵐ[mu.restrict Omega] fun s ↦
      weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u s 1 +
        A s (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u s) := by
  rw [trajectoryOperator_apply]
  filter_upwards [Lp.coeFn_add
    ((ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLp
      (weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u))
    ((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p A
      (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u)),
    (ContinuousLinearMap.apply ℝ F (1 : ℝ)).coeFn_compLp
      (weakFDeriv (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u),
    (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).coeFn_holder (r := p) A
      (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u)] with s hs hd hA
  exact hs.trans (by simp only [Pi.add_apply, hd, hA,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.id_apply])

/-- The operator norm of the first-order trajectory operator is at most `1 + ‖A‖`. -/
theorem norm_trajectoryOperator_le (A : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    ‖trajectoryOperator (p := p) A‖ ≤ 1 + ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [trajectoryOperator_apply]
  let base := ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))
  have hd : ‖(ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLp
      (weakFDeriv base u)‖ ≤ ‖u‖ := by
    have heval : ‖ContinuousLinearMap.apply ℝ F (1 : ℝ)‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro T
      simpa using T.le_opNorm (1 : ℝ)
    calc
      _ ≤ ‖ContinuousLinearMap.apply ℝ F (1 : ℝ)‖ * ‖weakFDeriv base u‖ :=
        ContinuousLinearMap.norm_compLp_le _ _
      _ ≤ 1 * ‖weakFDeriv base u‖ := by gcongr
      _ ≤ ‖u‖ := by simpa using norm_weakFDeriv_le base u
  have hA : ‖(ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p A
      (prev base u)‖ ≤ ‖A‖ * ‖u‖ := by
    calc
      _ ≤ ‖ContinuousLinearMap.id ℝ (F →L[ℝ] F)‖ * ‖A‖ * ‖prev base u‖ :=
        ContinuousLinearMap.norm_holder_apply_apply_le _ _ _
      _ ≤ 1 * ‖A‖ * ‖prev base u‖ := by
        gcongr
        exact ContinuousLinearMap.norm_id_le
      _ ≤ ‖A‖ * ‖u‖ := by
        simp only [one_mul]
        gcongr
        exact norm_prev_le base u
  calc
    _ ≤ ‖(ContinuousLinearMap.apply ℝ F (1 : ℝ)).compLp (weakFDeriv base u)‖ +
      ‖(ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p A (prev base u)‖ := norm_add_le _ _
    _ ≤ ‖u‖ + ‖A‖ * ‖u‖ := add_le_add hd hA
    _ = (1 + ‖A‖) * ‖u‖ := by ring

/-- Subtracting two trajectory operators cancels the derivative part and leaves multiplication
by the difference of their coefficients. -/
lemma trajectoryOperator_sub (A B : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    trajectoryOperator (p := p) A - trajectoryOperator B =
      ((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holderL (mu.restrict Omega) ∞ p p (A - B)).comp
        (prevL (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))) := by
  simp only [trajectoryOperator, map_sub, ContinuousLinearMap.sub_comp]
  abel

/-- An `L∞` perturbation of the coefficient changes the trajectory operator by at most the same
amount in operator norm. -/
theorem norm_trajectoryOperator_sub_le (A B : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) :
    ‖trajectoryOperator (p := p) A - trajectoryOperator B‖ ≤ ‖A - B‖ := by
  rw [trajectoryOperator_sub]
  have hprev : ‖prevL (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    simpa using norm_prev_le (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u
  calc
    _ ≤ ‖(ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holderL
        (mu.restrict Omega) ∞ p p (A - B)‖ *
      ‖prevL (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (1 * ‖A - B‖) * 1 := by
      gcongr
      exact ((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holderL
        (mu.restrict Omega) ∞ p p).le_opNorm (A - B) |>.trans (by
          gcongr
          exact (ContinuousLinearMap.norm_holderL_le _).trans ContinuousLinearMap.norm_id_le)
    _ = ‖A - B‖ := by ring

/-- The trajectory operator depends `1`-Lipschitz continuously on its `L∞` coefficient, for the
operator norm. -/
theorem lipschitzWith_trajectoryOperator :
    LipschitzWith 1 (trajectoryOperator (F := F) (mu := mu) (Omega := Omega) (p := p)) :=
  LipschitzWith.of_dist_le_mul fun A B ↦ by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using norm_trajectoryOperator_sub_le A B

/-- Solving the bounded trajectory equation is equivalent to solving the weak ordinary
differential equation `u' = f - A u`. -/
theorem trajectoryOperator_eq_iff_hasWeakLineDerivOn
    (A : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))))
    (f : Lp F p (mu.restrict Omega)) :
    trajectoryOperator A u = f ↔ HasWeakLineDerivOn mu Omega
      (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u : Lp F p (mu.restrict Omega))
      (fun s ↦ f s - A s (prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u s))
      1 := by
  let base := ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))
  have hd : HasWeakLineDerivOn mu Omega (prev base u : Lp F p (mu.restrict Omega))
      (fun s ↦ weakFDeriv base u s 1) 1 := by
    simpa only [base, ContinuousLinearMap.id_apply] using
      (hasWeakFDerivOn_base_prev base u).hasWeakLineDerivOn 1
  constructor
  · intro h
    apply hd.congr_ae_deriv
    have hformula := trajectoryOperator_apply_ae A u
    rw [h] at hformula
    filter_upwards [hformula] with s hs
    exact eq_sub_iff_add_eq.mpr hs.symm
  · intro h
    apply Lp.ext
    filter_upwards [trajectoryOperator_apply_ae A u, hd.ae_eq h] with s hs hd'
    rw [hs, hd']
    exact sub_add_cancel _ _

/-- **Weak solutions are values of graph elements.** If an `Lᵖ` path `x` has weak derivative
`f - A x`, then `x` is the value of an element `u` of the weak-derivative graph with
`D_A u = f`. This is the converse of `trajectoryOperator_eq_iff_hasWeakLineDerivOn`: there the
element `u` is given, here it is constructed from `x`. -/
theorem exists_prev_eq_and_trajectoryOperator_eq_of_hasWeakLineDerivOn
    (A : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega)) {x f : Lp F p (mu.restrict Omega)}
    (h : HasWeakLineDerivOn mu Omega (x : ℝ → F) (fun s ↦ f s - A s (x s)) 1) :
    ∃ u, prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u = x ∧
      trajectoryOperator A u = f := by
  let g := f - (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p A x
  -- The weak derivative `g` as an `Lᵖ` path of linear maps `ℝ →L[ℝ] F`.
  let lift := (ContinuousLinearMap.toSpanSingletonLIE ℝ F).toLinearIsometry.toContinuousLinearMap
  have hg : (fun s ↦ f s - A s (x s)) =ᵐ[mu.restrict Omega] g := by
    filter_upwards [Lp.coeFn_sub f ((ContinuousLinearMap.id ℝ (F →L[ℝ] F)).holder p A x),
      (ContinuousLinearMap.id ℝ (F →L[ℝ] F)).coeFn_holder (r := p) A x] with s hs hAs
    simp only [g, hs, Pi.sub_apply, hAs, ContinuousLinearMap.id_apply]
  have hD : HasWeakFDerivOn mu Omega (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega)) x)
      (lift.compLp g) := by
    rw [hasWeakFDerivOn_iff]
    intro r
    refine (by simpa using (h.congr_ae_deriv hg).smul_direction r :
      HasWeakLineDerivOn _ _ _ _ r).congr_ae_deriv ?_
    filter_upwards [lift.coeFn_compLp g] with s hs
    simp [lift, hs]
  refine ⟨mk _ x _ hD, prev_mk _ _ _ _, ?_⟩
  rw [trajectoryOperator_eq_iff_hasWeakLineDerivOn, prev_mk]
  exact h

end TauCeti.WeakDerivStep

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace
open scoped ENNReal

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {mu : Measure ℝ} [mu.IsAddHaarMeasure] {Omega : Opens ℝ}
  {p : ENNReal} [Fact (1 ≤ p)]

/-- For a differentiable representative whose derivative is locally integrable, the Sobolev
trajectory operator agrees almost everywhere with the classical expression `v' + A v`. -/
theorem trajectoryOperator_apply_ae_eq_deriv_add
    (A : Lp (F →L[ℝ] F) ∞ (mu.restrict Omega))
    (u : WeakDerivStep mu Omega p (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))))
    {v : ℝ → F}
    (hv : prev (ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))) u =ᵐ[mu.restrict Omega] v)
    (hdv : LocallyIntegrableOn (fderiv ℝ v) Omega mu)
    (hvd : ∀ s ∈ (Omega : Set ℝ), DifferentiableAt ℝ v s) :
    trajectoryOperator A u =ᵐ[mu.restrict Omega] fun s ↦ deriv v s + A s (v s) := by
  let base := ContinuousLinearMap.id ℝ (Lp F p (mu.restrict Omega))
  have hweak : HasWeakFDerivOn mu Omega v (weakFDeriv base u) := by
    have h := hasWeakFDerivOn_base_prev base u
    simp only [base, ContinuousLinearMap.id_apply] at h
    exact h.congr_ae hv
  filter_upwards [trajectoryOperator_apply_ae A u, hweak.ae_eq_fderiv hdv hvd, hv]
    with s hs hd hs'
  rw [hs, hd, hs', fderiv_apply_one_eq_deriv]

end TauCeti.WeakDerivStep
