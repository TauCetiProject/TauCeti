/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import TauCeti.Analysis.Fredholm.Criteria
public import TauCeti.Analysis.ODE.GreenIntegral
public import TauCeti.Analysis.ODE.TrajectoryOperator
public import TauCeti.Analysis.Sobolev.GraphStep.Density
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index

/-!
# The trajectory operator of a constant hyperbolic coefficient

Let `A` be a bounded operator on a real Banach space `X` whose flow `exp (t A)` has an exponential
dichotomy: for a bounded operator `P` commuting with `A`, constants `K` and `α > 0`,

`‖exp (t A) (P v)‖ ≤ K exp (-α t) ‖v‖` for `t ≥ 0`, and
`‖exp (t A) (v - P v)‖ ≤ K exp (α t) ‖v‖` for `t ≤ 0`.

These are the hypotheses of the Lyapunov--Perron construction in
`TauCeti.Analysis.ODE.LyapunovPerron.Basic`. Classically, on a finite-dimensional space they hold
for the spectral projection `P` onto the generalized eigenspaces of eigenvalues of negative real
part whenever `A` has no eigenvalue on the imaginary axis; that existence statement is not proved
here, and the results below take the estimates as hypotheses. The projection `P` need not be
idempotent for any of them.

The whole-line Green integral `ContinuousLinearMap.greenIntegral` of such a dichotomy, from
`TauCeti.Analysis.ODE.GreenIntegral`, is bounded on every `Lᵖ`, solves `u' = A u + g` for a
bounded continuous forcing term `g`, and recovers every compactly supported `C¹` path `u` from
`u' - A u`. For a Banach space `X`, it provides a `W^{1,p}` solution of `u' - A u = f` for every
continuous compactly supported `f`
(`TauCeti.WeakDerivStep.exists_prev_ae_eq_greenIntegral_and_trajectoryOperator_ae_eq`).

For a finite-dimensional `X` and `1 ≤ p < ∞` this shows that the trajectory operator
`d/ds - A : W^{1,p}(ℝ, X) → Lᵖ(ℝ, X)` (`TauCeti.WeakDerivStep.trajectoryOperator` of the
constant coefficient `-A`) is bijective. The representation formula gives the estimate
`‖u‖_{Lᵖ} ≤ 2 K / α ‖u' - A u‖_{Lᵖ}` on smooth compactly supported paths, which extends to
`W^{1,p}(ℝ, X)` by density, so the operator is injective with closed range; its range contains
every smooth compactly supported path, hence is dense. In particular it is Fredholm of index zero.
This is the constant-coefficient, whole-line case of the Fredholm theory of `d/ds - A(s)` with
hyperbolic limits; neither symmetry of `A` nor an inner product is used.

## Main declarations

* `TauCeti.WeakDerivStep.exists_prev_ae_eq_greenIntegral_and_trajectoryOperator_ae_eq`: the
  Green integral of a continuous compactly supported `f` is a `W^{1,p}` solution of `u' - A u = f`.
* `TauCeti.WeakDerivStep.norm_prev_le_mul_norm_trajectoryOperator_of_dichotomy`: the a priori
  estimate `‖u‖_{Lᵖ} ≤ 2 K / α ‖u' - A u‖_{Lᵖ}` on `W^{1,p}(ℝ, X)`.
* `TauCeti.WeakDerivStep.bijective_trajectoryOperator_of_dichotomy`: `d/ds - A` is bijective.
* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_of_dichotomy` and
  `TauCeti.WeakDerivStep.index_trajectoryOperator_eq_zero_of_dichotomy`: it is Fredholm of index
  zero.

## References

* W. A. Coppel, *Dichotomies in Stability Theory*, Lecture Notes in Mathematics **629**,
  Springer (1978) (exponential dichotomies and the Green function of `u' = A u + g`).
* K. J. Palmer, *Exponential dichotomies and transversal homoclinic points*, J. Differential
  Equations **55** (1984), 225--256 (the operator `u ↦ u' - A(t) u` under exponential
  dichotomies, and its Fredholm property).
-/

public section

noncomputable section

open Filter MeasureTheory NormedSpace Set Topology TopologicalSpace
open scoped NNReal ENNReal

/-! ### The trajectory operator `d/ds - A` on `W^{1,p}(ℝ, X)` -/

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {A P : E →L[ℝ] E} {K α : ℝ≥0}
  {AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))}

section Dichotomy

variable (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : E, ‖exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
  (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : E, ‖exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
  (hα : 0 < α)
  (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun _ ↦ -A)
include hs hu hα hAL

/-- **The Green integral is a `W^{1,p}` solution.** Under an exponential dichotomy for
`exp (t A)` on a Banach space `E`, for every continuous compactly supported `f` and
`1 ≤ p ≤ ∞`, some `u ∈ W^{1,p}(ℝ, E)` represented by the Green integral of `f` solves
`u' - A u = f`. -/
theorem exists_prev_ae_eq_greenIntegral_and_trajectoryOperator_ae_eq [CompleteSpace E]
    {f : ℝ → E} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ u : WeakDerivStep volume ⊤ p
        (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))),
      ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
          ContinuousLinearMap.greenIntegral A P f ∧
        ⇑(trajectoryOperator AL u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] f := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
  set v := ContinuousLinearMap.greenIntegral A P f
  have hv (s : ℝ) : HasDerivAt v (A (v s) + f s) s :=
    ContinuousLinearMap.hasDerivAt_greenIntegral hs hu hα hf hM s
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun s ↦ (hv s).continuousAt
  have hfp : MemLp f p volume := hf.memLp_of_hasCompactSupport hfc
  have hvp : MemLp v p volume :=
    (ContinuousLinearMap.eLpNorm_greenIntegral_le hs hu hα hf hM Fact.out).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfp.eLpNorm_lt_top)
  have hvp' : MemLp v p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by simpa using hvp
  have hfp' : MemLp f p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)) := by simpa using hfp
  have hx := hvp'.coeFn_toLp
  have hy := hfp'.coeFn_toLp
  have h : HasWeakLineDerivOn volume ⊤ v (fun s ↦ A (v s) + f s) 1 :=
    hasWeakLineDerivOn_of_hasLineDerivAt ((hvp.locallyIntegrable Fact.out).locallyIntegrableOn _)
      (((A.continuous.comp hvc).add hf).locallyIntegrable.locallyIntegrableOn _)
      fun s _ ↦ by simpa using (hv s).hasFDerivAt.hasLineDerivAt 1
  -- In the form `u' = f - AL u` used by the trajectory operator.
  have hd : (fun s ↦ A (v s) + f s) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
      fun s ↦ hfp'.toLp f s - AL s (hvp'.toLp v s) := by
    filter_upwards [hAL, hx, hy] with s hAs hxs hys
    rw [hAs, hxs, hys, neg_apply, sub_neg_eq_add, add_comm]
  obtain ⟨u, hux, hu'⟩ := exists_prev_eq_and_trajectoryOperator_eq_of_hasWeakLineDerivOn AL
    ((h.congr_ae hx.symm).congr_ae_deriv hd)
  exact ⟨u, by rw [hux]; exact hx, by rw [hu']; exact hy⟩

variable [FiniteDimensional ℝ E]

/-- **The a priori estimate for `d/ds - A`.** Under an exponential dichotomy for `exp (t A)` with
constant `K` and rate `α > 0`, and `1 ≤ p < ∞`, every `u ∈ W^{1,p}(ℝ, E)` satisfies
`‖u‖_{Lᵖ} ≤ 2 K / α ‖u' - A u‖_{Lᵖ}`. The coefficient of the trajectory operator is any `L∞`
class `AL` of the constant `-A`. -/
theorem norm_prev_le_mul_norm_trajectoryOperator_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖prev _ u‖ ≤ 2 * K / α * ‖trajectoryOperator AL u‖ := by
  -- Abstract the base map before introducing `u`, so that the closed set below and the density
  -- statement are stated over the same graph space.
  revert u
  set base := ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
  intro u
  -- The estimate is a closed condition, so it suffices to prove it on smooth compactly supported
  -- paths, where it is the `Lᵖ` bound for the Green integral.
  have hclosed : IsClosed {u : WeakDerivStep volume ⊤ p base |
      ‖prev base u‖ ≤ 2 * K / α * ‖trajectoryOperator AL u‖} :=
    isClosed_le ((prevL base).continuous.congr fun u ↦ prevL_apply base u).norm
      (continuous_const.mul (trajectoryOperator AL).continuous.norm)
  refine hclosed.closure_subset_iff.mpr ?_ (dense_setOf_exists_contDiff_hasCompactSupport hp u)
  rintro u ⟨φ, hφ, hφc, huφ⟩
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  set g : ℝ → E := fun s ↦ deriv φ s - A (φ s) with g_def
  have hgc : Continuous g := (hφ1.continuous_deriv le_rfl).sub (A.continuous.comp hφ1.continuous)
  have hgs : HasCompactSupport g := hφc.deriv.sub (hφc.comp_left (map_zero A))
  have hgp : MemLp g p volume := hgc.memLp_of_hasCompactSupport hgs
  have hTu : trajectoryOperator AL u =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] g := by
    filter_upwards [trajectoryOperator_apply_ae_eq_deriv_add AL u huφ
      ((hφ1.continuous_fderiv one_ne_zero).locallyIntegrable.locallyIntegrableOn _)
      (fun s _ ↦ hφ1.differentiable one_ne_zero s), hAL] with s hs' hAs
    rw [hs', hAs, neg_apply, ← sub_eq_add_neg]
  have hG : ContinuousLinearMap.greenIntegral A P g = φ :=
    funext (ContinuousLinearMap.greenIntegral_deriv_sub_eq hAP hφ1 hφc)
  obtain ⟨M, hM⟩ := hgc.bounded_above_of_compact_support hgs
  have key := ContinuousLinearMap.eLpNorm_greenIntegral_le hs hu hα hgc hM (p := p) Fact.out
  rw [hG] at key
  rw [Set.mem_ofPred_eq, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae huφ, eLpNorm_congr_ae hTu]
  simp only [Opens.coe_top, Measure.restrict_univ]
  calc (eLpNorm φ p volume).toReal
      ≤ (ENNReal.ofReal (2 * K / α) * eLpNorm g p volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgp.eLpNorm_ne_top) key
    _ = 2 * K / α * (eLpNorm g p volume).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- **The graph-norm estimate for `d/ds - A`.** Under an exponential dichotomy for `exp (t A)`
with constant `K` and rate `α > 0`, and `1 ≤ p < ∞`, every `u ∈ W^{1,p}(ℝ, E)` satisfies
`‖u‖ ≤ (1 + (1 + ‖AL‖) 2 K / α) ‖u' - A u‖_{Lᵖ}`, where `AL` is the `L∞` class of `-A`. -/
theorem norm_le_mul_norm_trajectoryOperator_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P)
    (u : WeakDerivStep volume ⊤ p
      (ContinuousLinearMap.id ℝ (Lp E p (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))) :
    ‖u‖ ≤ (1 + (1 + ‖AL‖) * (2 * K / α)) * ‖trajectoryOperator AL u‖ := by
  have hprev := norm_prev_le_mul_norm_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP u
  have hweak := norm_weakFDeriv_le_norm_trajectoryOperator_add AL u
  have hsum : ‖u‖ ≤ ‖prev _ u‖ + ‖weakFDeriv _ u‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg u) (by positivity) two_ne_zero).mp ?_
    rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq]
    nlinarith [norm_nonneg (prev _ u), norm_nonneg (weakFDeriv _ u)]
  have hAL0 := norm_nonneg AL
  calc ‖u‖ ≤ ‖trajectoryOperator AL u‖ + (1 + ‖AL‖) * ‖prev _ u‖ := by linarith
    _ ≤ ‖trajectoryOperator AL u‖ + (1 + ‖AL‖) * (2 * K / α * ‖trajectoryOperator AL u‖) := by
      gcongr
    _ = (1 + (1 + ‖AL‖) * (2 * K / α)) * ‖trajectoryOperator AL u‖ := by ring

/-- **`d/ds - A` is injective.** Under an exponential dichotomy for `exp (t A)` and `1 ≤ p < ∞`,
`u' = A u` has no nonzero solution in `W^{1,p}(ℝ, E)`. -/
theorem injective_trajectoryOperator_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P) :
    Function.Injective (trajectoryOperator (p := p) AL) := by
  refine (injective_iff_map_eq_zero _).2 fun u hu0 ↦ norm_le_zero_iff.1 ?_
  simpa [hu0] using norm_le_mul_norm_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP u

/-- **`d/ds - A` is surjective.** Under an exponential dichotomy for `exp (t A)` and
`1 ≤ p < ∞`, the equation `u' - A u = f` has a solution `u ∈ W^{1,p}(ℝ, E)` for every
`f ∈ Lᵖ(ℝ, E)`. -/
theorem surjective_trajectoryOperator_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P) :
    Function.Surjective (trajectoryOperator (p := p) AL) := by
  set C : ℝ≥0 := ⟨1 + (1 + ‖AL‖) * (2 * K / α), by positivity⟩
  have hanti : AntilipschitzWith C (trajectoryOperator (p := p) AL) :=
    (trajectoryOperator (p := p) AL).antilipschitz_of_bound
      (norm_le_mul_norm_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP)
  have hclosed : IsClosed (range (trajectoryOperator (p := p) AL)) :=
    hanti.isClosed_range (trajectoryOperator (p := p) AL).uniformContinuous
  -- The range contains every smooth compactly supported path, and these are dense in `Lᵖ`.
  have hdense : Dense (range (trajectoryOperator (p := p) AL)) := by
    refine (Lp.dense_hasCompactSupport_contDiff hp).mono ?_
    rintro f ⟨g, hfg, hgc, hg⟩
    obtain ⟨u, -, hTu⟩ := exists_prev_ae_eq_greenIntegral_and_trajectoryOperator_ae_eq
      (p := p) (P := P) hs hu hα hAL hg.continuous hgc
    exact ⟨u, Lp.ext (hTu.trans hfg.symm)⟩
  exact range_eq_univ.mp (hclosed.closure_eq.symm.trans hdense.closure_eq)

/-- **`d/ds - A` is bijective.** Under an exponential dichotomy for `exp (t A)` and
`1 ≤ p < ∞`, the trajectory operator `u ↦ u' - A u` is a bijection from `W^{1,p}(ℝ, E)` onto
`Lᵖ(ℝ, E)`. -/
theorem bijective_trajectoryOperator_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P) :
    Function.Bijective (trajectoryOperator (p := p) AL) :=
  ⟨injective_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP,
    surjective_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP⟩

/-- **`d/ds - A` is Fredholm.** Under an exponential dichotomy for `exp (t A)` and `1 ≤ p < ∞`,
the trajectory operator `u ↦ u' - A u` from `W^{1,p}(ℝ, E)` to `Lᵖ(ℝ, E)` is Fredholm. -/
theorem isFredholm_trajectoryOperator_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P) :
    (trajectoryOperator (p := p) AL).IsFredholm :=
  .of_bijective (bijective_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP)

/-- **`d/ds - A` has index zero.** Under an exponential dichotomy for `exp (t A)` and
`1 ≤ p < ∞`, the trajectory operator `u ↦ u' - A u` from `W^{1,p}(ℝ, E)` to `Lᵖ(ℝ, E)` has
Fredholm index zero. -/
theorem index_trajectoryOperator_eq_zero_of_dichotomy (hp : p ≠ ∞) (hAP : Commute A P) :
    (trajectoryOperator (p := p) AL).index = 0 :=
  ContinuousLinearMap.index_eq_zero_of_bijective _
    (bijective_trajectoryOperator_of_dichotomy hs hu hα hAL hp hAP)

end Dichotomy

end TauCeti.WeakDerivStep
