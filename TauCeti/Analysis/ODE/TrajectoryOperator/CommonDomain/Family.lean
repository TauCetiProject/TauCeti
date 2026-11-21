/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain
public import TauCeti.MeasureTheory.Function.Lp.Operator.LpMultiplication
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The trajectory operator of a family of operators over a common domain

Let `ι : D →L[ℝ] H` embed a Banach space `D` into a Banach space `H`, and let
`A : ℝ → (D →L[ℝ] H)` be an essentially bounded, strongly measurable family of operators, given as
a class in `L∞(Ω, D →L[ℝ] H)`. For instance `A(s)` can be an unbounded operator on `H`, such as
`J ∂ₜ + S(s, t)` acting on paths `t ↦ ξ(t)` with `D = H¹` and `H = L²`, which is bounded only as a
map from its domain `D`. On `Lᵖ(Ω, D) ∩ W^{1,p}(Ω, H)`, realized as
`WeakDerivStep mu Omega p (ι.compLpL p (mu.restrict Omega))`, the operator

`u ↦ (ι ∘ u)' + A(s) u(s)`

is a bounded map `TauCeti.WeakDerivStep.familyDomainTrajectoryOperator ι A` into `Lᵖ(Ω, H)`, the
coefficient acting by `MeasureTheory.Lp.operatorMultiplication`.
It extends the autonomous operator `TauCeti.WeakDerivStep.domainTrajectoryOperator ι A₀` of
`TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain`, which is the case of a constant
coefficient (`TauCeti.WeakDerivStep.familyDomainTrajectoryOperator_toLp_const`), and it is the
common-domain counterpart of the bounded `TauCeti.WeakDerivStep.trajectoryOperator`. As there, it
is `1`-Lipschitz in its `L∞` coefficient, and solving `familyDomainTrajectoryOperator ι A u = f`
is the weak equation `(ι ∘ u)' = f - A u`.

On the whole line in `L²`, the autonomous operator of an invertible `ι`-symmetric `A₀`
(`⟪A₀ x, ι y⟫ = ⟪ι x, A₀ y⟫`) is invertible with inverse of norm at most
`M = √(1 + ‖A₀⁻¹‖²)`. Comparing with it gives the estimates for a coefficient that is close to
`A₀`, without any symmetry of `A(s)` itself:

* if `‖A(s) - A₀‖ ≤ δ` for almost every `s` in a set `S` and the path `u` vanishes off `S`, then
  `(1 - M δ) ‖u‖ ≤ M ‖(ι ∘ u)' + A u‖`
  (`TauCeti.WeakDerivStep.mul_norm_le_mul_norm_familyDomainTrajectoryOperator`);
* if `M ‖A - A₀‖_{L∞} < 1`, the operator is invertible, with inverse of norm at most
  `M / (1 - M ‖A - A₀‖_{L∞})`
  (`TauCeti.WeakDerivStep.isInvertible_familyDomainTrajectoryOperator_of_mul_norm_sub_lt` and
  `TauCeti.WeakDerivStep.norm_inverse_familyDomainTrajectoryOperator_le`);
* if `A(s)` converges to an invertible `ι`-symmetric `B` as `s → ∞`, there are `C` and `T` with
  `‖u‖ ≤ C ‖(ι ∘ u)' + A u‖` for every path `u` vanishing on `(-∞, T)`
  (`exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atTop`),
  and likewise at `-∞`.

The last estimate is the control of the ends in the Fredholm theory of `∂ₛ + A(s)` for a family
with invertible limits `A±`: after cutting a path off near the two ends, only a piece supported in a
bounded interval remains, which is where the compactness of `D → H` enters.

## Main declarations

* `TauCeti.WeakDerivStep.familyDomainTrajectoryOperator`: the operator `u ↦ (ι ∘ u)' + A u`.
* `TauCeti.WeakDerivStep.familyDomainTrajectoryOperator_toLp_const`: a constant coefficient gives
  `TauCeti.WeakDerivStep.domainTrajectoryOperator`.
* `TauCeti.WeakDerivStep.lipschitzWith_familyDomainTrajectoryOperator`: `1`-Lipschitz dependence on
  the coefficient.
* `TauCeti.WeakDerivStep.familyDomainTrajectoryOperator_eq_iff_hasWeakLineDerivOn`: the weak
  equation.
* `TauCeti.WeakDerivStep.mul_norm_le_mul_norm_familyDomainTrajectoryOperator`: the estimate for
  paths supported where the coefficient is close to `A₀`.
* `TauCeti.WeakDerivStep.isInvertible_familyDomainTrajectoryOperator_of_mul_norm_sub_lt`:
  invertibility near an invertible symmetric constant.
* `exists_mem_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto`:
  the estimate for paths supported where `A` is near its limit along a filter, with the versions
  `exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atTop`
  and `..._atBot` at the two ends.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §3.
* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open Filter _root_.MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProductSpace Topology

section Banach

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "μΩ" => (mu.restrict Omega)

/-- The first-order operator `u ↦ (ι ∘ u)' + A(s) u(s)` from `Lᵖ(Ω, D) ∩ W^{1,p}(Ω, H)` to
`Lᵖ(Ω, H)`, for an `L∞` family `A` of operators from `D` to `H`. It depends only on the almost
everywhere class of `A`. -/
def familyDomainTrajectoryOperator (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ) :
    WeakDerivStep mu Omega p (ι.compLpL p μΩ) →L[ℝ] Lp H p μΩ :=
  ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ).comp (weakFDerivL (ι.compLpL p μΩ)) +
    (Lp.operatorMultiplication p A).comp (prevL (ι.compLpL p μΩ))

/-- Unfolding formula for `familyDomainTrajectoryOperator` as a continuous linear map. -/
theorem familyDomainTrajectoryOperator_def (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ) :
    familyDomainTrajectoryOperator (p := p) ι A =
      ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ).comp (weakFDerivL (ι.compLpL p μΩ)) +
        (Lp.operatorMultiplication p A).comp (prevL (ι.compLpL p μΩ)) := (rfl)

/-- `familyDomainTrajectoryOperator` adds weak-derivative evaluation at `1` to the action of the
coefficient. -/
@[simp] theorem familyDomainTrajectoryOperator_apply (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ)
    (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) :
    familyDomainTrajectoryOperator ι A u =
      (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ (weakFDeriv (ι.compLpL p μΩ) u) +
      Lp.operatorMultiplication p A (prev (ι.compLpL p μΩ) u) := by
  simp [familyDomainTrajectoryOperator_def]

/-- Pointwise almost-everywhere formula for `familyDomainTrajectoryOperator`. -/
theorem familyDomainTrajectoryOperator_apply_ae (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ)
    (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) :
    familyDomainTrajectoryOperator ι A u =ᵐ[μΩ]
      fun s ↦ weakFDeriv (ι.compLpL p μΩ) u s 1 + A s (prev (ι.compLpL p μΩ) u s) := by
  let base := ι.compLpL p μΩ
  rw [familyDomainTrajectoryOperator_apply]
  filter_upwards [Lp.coeFn_add ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ
      (weakFDeriv base u)) (Lp.operatorMultiplication p A (prev base u)),
    (ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLpL (weakFDeriv base u),
    Lp.operatorMultiplication_ae A (prev base u)] with s hadd hd hA
  rw [hadd, Pi.add_apply, hd, hA, ContinuousLinearMap.apply_apply]

/-- The operator norm of `familyDomainTrajectoryOperator ι A` is at most `1 + ‖A‖`. -/
theorem norm_familyDomainTrajectoryOperator_le (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ) :
    ‖familyDomainTrajectoryOperator (p := p) ι A‖ ≤ 1 + ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  rw [familyDomainTrajectoryOperator_apply]; refine (norm_add_le _ _).trans ?_
  rw [ContinuousLinearMap.norm_apply_one_compLpL_apply, one_add_mul]
  exact add_le_add (norm_weakFDeriv_le _ u) ((Lp.norm_operatorMultiplication_apply_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_prev_le _ u) (norm_nonneg _)))

/-- Subtracting two operators over the same domain embedding cancels the derivative part and
leaves the action of the difference of the coefficients. -/
theorem familyDomainTrajectoryOperator_sub (ι : D →L[ℝ] H) (A B : Lp (D →L[ℝ] H) ∞ μΩ) :
    familyDomainTrajectoryOperator (p := p) ι A - familyDomainTrajectoryOperator ι B =
      (Lp.operatorMultiplication p (A - B)).comp (prevL (ι.compLpL p μΩ)) := by
  simp only [familyDomainTrajectoryOperator, map_sub, ContinuousLinearMap.sub_comp]
  abel

/-- Changing the coefficient from `B` to `A` changes `familyDomainTrajectoryOperator ι` by at most
`‖A - B‖` in operator norm. -/
theorem norm_familyDomainTrajectoryOperator_sub_le (ι : D →L[ℝ] H) (A B : Lp (D →L[ℝ] H) ∞ μΩ) :
    ‖familyDomainTrajectoryOperator (p := p) ι A - familyDomainTrajectoryOperator ι B‖ ≤
      ‖A - B‖ := by
  rw [familyDomainTrajectoryOperator_sub]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u ↦ ?_
  rw [ContinuousLinearMap.comp_apply, prevL_apply]
  exact (Lp.norm_operatorMultiplication_apply_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_prev_le _ u) (norm_nonneg _))

/-- `familyDomainTrajectoryOperator ι` is `1`-Lipschitz in its `L∞` coefficient. -/
theorem lipschitzWith_familyDomainTrajectoryOperator (ι : D →L[ℝ] H) :
    LipschitzWith 1 (familyDomainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι) :=
  LipschitzWith.of_dist_le_mul fun A B ↦ by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
      norm_familyDomainTrajectoryOperator_sub_le ι A B

/-- `familyDomainTrajectoryOperator ι` depends continuously on its `L∞` coefficient. -/
@[fun_prop] theorem continuous_familyDomainTrajectoryOperator (ι : D →L[ℝ] H) :
    Continuous (familyDomainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι) :=
  (lipschitzWith_familyDomainTrajectoryOperator ι).continuous

/-- For the constant coefficient `A₀`, `familyDomainTrajectoryOperator` is the autonomous
operator `domainTrajectoryOperator ι A₀`. -/
theorem familyDomainTrajectoryOperator_toLp_const (ι A₀ : D →L[ℝ] H) :
    familyDomainTrajectoryOperator (p := p) ι ((memLp_top_const (μ := μΩ) A₀).toLp _) =
      domainTrajectoryOperator ι A₀ := by
  rw [familyDomainTrajectoryOperator_def, domainTrajectoryOperator_def,
    Lp.operatorMultiplication_of_ae_eq_const (memLp_top_const A₀).coeFn_toLp]

/-- `familyDomainTrajectoryOperator ι A u = f` iff `(ι ∘ u)' = f - A u` weakly. -/
theorem familyDomainTrajectoryOperator_eq_iff_hasWeakLineDerivOn (ι : D →L[ℝ] H)
    (A : Lp (D →L[ℝ] H) ∞ μΩ) (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) (f : Lp H p μΩ) :
    familyDomainTrajectoryOperator ι A u = f ↔ HasWeakLineDerivOn mu Omega
      (ι.compLpL p μΩ (prev (ι.compLpL p μΩ) u))
      (fun s ↦ f s - A s (prev (ι.compLpL p μΩ) u s)) 1 := by
  have hd := (hasWeakFDerivOn_base_prev (ι.compLpL p μΩ) u).hasWeakLineDerivOn 1
  refine ⟨fun h ↦ hd.congr_ae_deriv ?_, fun h ↦ Lp.ext ?_⟩
  · filter_upwards [h ▸ familyDomainTrajectoryOperator_apply_ae ι A u] with s hs
    exact eq_sub_iff_add_eq.mpr hs.symm
  · filter_upwards [familyDomainTrajectoryOperator_apply_ae ι A u, hd.ae_eq h] with s hs hd'
    rw [hs, hd', sub_add_cancel]

/-- If `x ∈ Lᵖ(Ω, D)` solves `(ι ∘ x)' = f - A x` weakly on `Ω`, then `x` lifts to `u` with
`familyDomainTrajectoryOperator ι A u = f`. -/
theorem exists_prev_eq_and_familyDomainTrajectoryOperator_eq_of_hasWeakLineDerivOn
    (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ) {x : Lp D p μΩ} {f : Lp H p μΩ}
    (h : HasWeakLineDerivOn mu Omega (ι.compLpL p μΩ x) (fun s ↦ f s - A s (x s)) 1) :
    ∃ u : WeakDerivStep mu Omega p (ι.compLpL p μΩ),
      prev (ι.compLpL p μΩ) u = x ∧ familyDomainTrajectoryOperator ι A u = f := by
  let g := f - Lp.operatorMultiplication p A x
  have hg : (fun s ↦ f s - A s (x s)) =ᵐ[μΩ] g := by
    filter_upwards [Lp.coeFn_sub f (Lp.operatorMultiplication p A x),
      Lp.operatorMultiplication_ae A x] with s hs hA
    simp only [g, hs, Pi.sub_apply, hA]
  refine ⟨mkLine _ x g (h.congr_ae_deriv hg), prev_mkLine _ _ _ _, ?_⟩
  rwa [familyDomainTrajectoryOperator_eq_iff_hasWeakLineDerivOn, prev_mkLine]

end Banach

section Symmetric

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι A₀ : D →L[ℝ] H}

omit [CompleteSpace D] in
/-- If `‖A(s) - A₀‖ ≤ δ` for almost every `s` in `S` and the path `u` vanishes almost everywhere
off `S`, the operators of `A` and of the constant `A₀` differ on `u` by at most `δ ‖u‖`. -/
private theorem norm_familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_le
    {A : Lp (D →L[ℝ] H) ∞ μ₀} {S : Set ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ∀ᵐ s ∂volume, s ∈ S → ‖A s - A₀‖ ≤ δ)
    {u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (hu : ∀ᵐ s ∂volume, s ∉ S → prev (ι.compLpL 2 μ₀) u s = 0) :
    ‖familyDomainTrajectoryOperator ι A u - domainTrajectoryOperator ι A₀ u‖ ≤ δ * ‖u‖ := by
  rw [← familyDomainTrajectoryOperator_toLp_const, ← sub_apply]
  refine (Lp.norm_le_mul_norm_of_ae_le_mul (g := prev (ι.compLpL 2 μ₀) u) ?_).trans
    (mul_le_mul_of_nonneg_left (norm_prev_le _ u) hδ)
  filter_upwards [familyDomainTrajectoryOperator_apply_ae ι A u,
    familyDomainTrajectoryOperator_apply_ae ι ((memLp_top_const (μ := μ₀) A₀).toLp _) u,
    (memLp_top_const (μ := μ₀) A₀).coeFn_toLp,
    Lp.coeFn_sub (familyDomainTrajectoryOperator ι A u)
      (familyDomainTrajectoryOperator ι ((memLp_top_const (μ := μ₀) A₀).toLp _) u),
    ae_restrict_of_ae hA, ae_restrict_of_ae hu] with s h₁ h₂ hc hsub hAs hus
  rw [sub_apply, hsub, Pi.sub_apply, h₁, h₂, hc, add_sub_add_left_eq_sub, ← sub_apply]
  by_cases hs : s ∈ S
  · exact ((A s - A₀).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hAs hs) (norm_nonneg _))
  · rw [hus hs]; simp

/-- **Estimate near an invertible symmetric constant.** Let `A₀` be invertible and `ι`-symmetric,
and put `M = √(1 + ‖A₀⁻¹‖²)`. If `‖A(s) - A₀‖ ≤ δ` for almost every `s` in `S` and the path `u`
vanishes almost everywhere off `S`, then `(1 - M δ) ‖u‖ ≤ M ‖(ι ∘ u)' + A u‖` on `L²(ℝ)`. -/
theorem mul_norm_le_mul_norm_familyDomainTrajectoryOperator
    (hSymm : ∀ x y : D, ⟪A₀ x, ι y⟫_ℝ = ⟪ι x, A₀ y⟫_ℝ) (hA₀ : A₀.IsInvertible)
    {A : Lp (D →L[ℝ] H) ∞ μ₀} {S : Set ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ∀ᵐ s ∂volume, s ∈ S → ‖A s - A₀‖ ≤ δ)
    {u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀)}
    (hu : ∀ᵐ s ∂volume, s ∉ S → prev (ι.compLpL 2 μ₀) u s = 0) :
    (1 - √(1 + ‖A₀.inverse‖ ^ 2) * δ) * ‖u‖ ≤
      √(1 + ‖A₀.inverse‖ ^ 2) * ‖familyDomainTrajectoryOperator ι A u‖ := by
  set M := √(1 + ‖A₀.inverse‖ ^ 2)
  have h₀ := norm_le_sqrt_one_add_sq_mul_norm_domainTrajectoryOperator hSymm hA₀ u
  have hdiff :=
    norm_familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_le (ι := ι) hδ hA hu
  have htri : ‖domainTrajectoryOperator ι A₀ u‖ ≤
      ‖familyDomainTrajectoryOperator ι A u‖ + δ * ‖u‖ := by
    have := norm_sub_le (familyDomainTrajectoryOperator ι A u)
      (familyDomainTrajectoryOperator ι A u - domainTrajectoryOperator ι A₀ u)
    rw [sub_sub_cancel] at this
    linarith
  nlinarith [mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg (1 + ‖A₀.inverse‖ ^ 2))]

omit [CompleteSpace D] in
/-- The difference between `familyDomainTrajectoryOperator ι A` and the autonomous operator of
`A₀` has norm at most `‖A - A₀‖_{L∞}`. -/
private theorem norm_familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_le_norm
    (A : Lp (D →L[ℝ] H) ∞ μ₀) :
    ‖familyDomainTrajectoryOperator (p := 2) ι A - domainTrajectoryOperator ι A₀‖ ≤
      ‖A - (memLp_top_const (μ := μ₀) A₀).toLp _‖ := by
  rw [← familyDomainTrajectoryOperator_toLp_const]
  exact norm_familyDomainTrajectoryOperator_sub_le ι _ _

/-- **Invertibility near an invertible symmetric constant.** If `A₀` is invertible and
`ι`-symmetric and `√(1 + ‖A₀⁻¹‖²) ‖A - A₀‖_{L∞} < 1`, then `u ↦ (ι ∘ u)' + A u` is invertible from
`L²(ℝ, D) ∩ W^{1,2}(ℝ, H)` onto `L²(ℝ, H)`. -/
theorem isInvertible_familyDomainTrajectoryOperator_of_mul_norm_sub_lt
    (hSymm : ∀ x y : D, ⟪A₀ x, ι y⟫_ℝ = ⟪ι x, A₀ y⟫_ℝ) (hA₀ : A₀.IsInvertible)
    {A : Lp (D →L[ℝ] H) ∞ μ₀}
    (h : √(1 + ‖A₀.inverse‖ ^ 2) * ‖A - (memLp_top_const (μ := μ₀) A₀).toLp _‖ < 1) :
    (familyDomainTrajectoryOperator (p := 2) ι A).IsInvertible :=
  (isInvertible_domainTrajectoryOperator hSymm hA₀).of_mul_norm_sub_lt
    (norm_inverse_domainTrajectoryOperator_le hSymm hA₀)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (norm_familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_le_norm (ι := ι)
        (A₀ := A₀) A) (Real.sqrt_nonneg _)) h)

/-- Under the hypotheses of
`isInvertible_familyDomainTrajectoryOperator_of_mul_norm_sub_lt`, with
`M = √(1 + ‖A₀⁻¹‖²)`, the inverse of `u ↦ (ι ∘ u)' + A u` has norm at most
`M / (1 - M ‖A - A₀‖_{L∞})`. -/
theorem norm_inverse_familyDomainTrajectoryOperator_le
    (hSymm : ∀ x y : D, ⟪A₀ x, ι y⟫_ℝ = ⟪ι x, A₀ y⟫_ℝ) (hA₀ : A₀.IsInvertible)
    {A : Lp (D →L[ℝ] H) ∞ μ₀}
    (h : √(1 + ‖A₀.inverse‖ ^ 2) * ‖A - (memLp_top_const (μ := μ₀) A₀).toLp _‖ < 1) :
    ‖(familyDomainTrajectoryOperator (p := 2) ι A).inverse‖ ≤
      √(1 + ‖A₀.inverse‖ ^ 2) /
        (1 - √(1 + ‖A₀.inverse‖ ^ 2) * ‖A - (memLp_top_const (μ := μ₀) A₀).toLp _‖) := by
  have hle := mul_le_mul_of_nonneg_left
    (norm_familyDomainTrajectoryOperator_sub_domainTrajectoryOperator_le_norm (ι := ι)
      (A₀ := A₀) A)
    (Real.sqrt_nonneg (1 + ‖A₀.inverse‖ ^ 2))
  refine ((isInvertible_domainTrajectoryOperator hSymm hA₀).norm_inverse_le_of_mul_norm_sub_lt
    (norm_inverse_domainTrajectoryOperator_le hSymm hA₀) (lt_of_le_of_lt hle h)).trans ?_
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (sub_pos.2 h) (by linarith)

/-- **The estimate along a filter.** If `A(s)` converges along a filter `l` on `ℝ` to an invertible
`ι`-symmetric operator `A₀`, there are a set `S ∈ l` and a constant `C` with
`‖u‖ ≤ C ‖(ι ∘ u)' + A u‖` on `L²(ℝ)` for every path `u` vanishing almost everywhere off `S`. -/
theorem exists_mem_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto
    (hSymm : ∀ x y : D, ⟪A₀ x, ι y⟫_ℝ = ⟪ι x, A₀ y⟫_ℝ) (hA₀ : A₀.IsInvertible)
    {A : ℝ → D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀} (hAL : AL =ᵐ[μ₀] A) {l : Filter ℝ}
    (hA : Tendsto A l (𝓝 A₀)) :
    ∃ C : ℝ, ∃ S ∈ l, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, s ∉ S → prev (ι.compLpL 2 μ₀) u s = 0) →
        ‖u‖ ≤ C * ‖familyDomainTrajectoryOperator ι AL u‖ := by
  set M := √(1 + ‖A₀.inverse‖ ^ 2)
  have hM : 0 < M := Real.sqrt_pos.2 (by positivity)
  have hδ : 0 < (2 * M)⁻¹ := by positivity
  refine ⟨2 * M, {s | ‖A s - A₀‖ ≤ (2 * M)⁻¹},
    (hA.eventually (Metric.closedBall_mem_nhds A₀ hδ)).mono fun s hs ↦ by
      simpa [dist_eq_norm] using hs, fun u hu ↦ ?_⟩
  have hae : ae volume = ae μ₀ := by simp
  have hAs : ∀ᵐ s ∂volume, s ∈ {s | ‖A s - A₀‖ ≤ (2 * M)⁻¹} → ‖AL s - A₀‖ ≤ (2 * M)⁻¹ := by
    filter_upwards [hAL.filter_mono hae.le] with s hs h
    rwa [hs]
  have := mul_norm_le_mul_norm_familyDomainTrajectoryOperator hSymm hA₀ hδ.le hAs hu
  rw [show M * (2 * M)⁻¹ = 1 / 2 by field_simp] at this
  linarith

/-- **The estimate at `+∞`.** If `A(s)` converges as `s → ∞` to an invertible `ι`-symmetric
operator `B`, there are `C` and `T` with `‖u‖ ≤ C ‖(ι ∘ u)' + A u‖` on `L²(ℝ)` for every path `u`
vanishing almost everywhere on `(-∞, T)`. -/
theorem exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atTop
    {B : D →L[ℝ] H} (hSymm : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (hB : B.IsInvertible) {A : ℝ → D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀} (hAL : AL =ᵐ[μ₀] A)
    (hA : Tendsto A atTop (𝓝 B)) :
    ∃ C T : ℝ, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, s < T → prev (ι.compLpL 2 μ₀) u s = 0) →
        ‖u‖ ≤ C * ‖familyDomainTrajectoryOperator ι AL u‖ := by
  obtain ⟨C, S, hS, hC⟩ :=
    exists_mem_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto hSymm hB hAL hA
  obtain ⟨T, hT⟩ := mem_atTop_sets.1 hS
  exact ⟨C, T, fun u hu ↦ hC u (hu.mono fun s hs hsS ↦
    hs (lt_of_not_ge fun h ↦ hsS (hT s h)))⟩

/-- **The estimate at `-∞`.** If `A(s)` converges as `s → -∞` to an invertible `ι`-symmetric
operator `B`, there are `C` and `T` with `‖u‖ ≤ C ‖(ι ∘ u)' + A u‖` on `L²(ℝ)` for every path `u`
vanishing almost everywhere on `(T, ∞)`. -/
theorem exists_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto_atBot
    {B : D →L[ℝ] H} (hSymm : ∀ x y : D, ⟪B x, ι y⟫_ℝ = ⟪ι x, B y⟫_ℝ)
    (hB : B.IsInvertible) {A : ℝ → D →L[ℝ] H} {AL : Lp (D →L[ℝ] H) ∞ μ₀} (hAL : AL =ᵐ[μ₀] A)
    (hA : Tendsto A atBot (𝓝 B)) :
    ∃ C T : ℝ, ∀ u : WeakDerivStep volume ⊤ 2 (ι.compLpL 2 μ₀),
      (∀ᵐ s ∂volume, T < s → prev (ι.compLpL 2 μ₀) u s = 0) →
        ‖u‖ ≤ C * ‖familyDomainTrajectoryOperator ι AL u‖ := by
  obtain ⟨C, S, hS, hC⟩ :=
    exists_mem_forall_norm_le_mul_norm_familyDomainTrajectoryOperator_of_tendsto hSymm hB hAL hA
  obtain ⟨T, hT⟩ := mem_atBot_sets.1 hS
  exact ⟨C, T, fun u hu ↦ hC u (hu.mono fun s hs hsS ↦
    hs (lt_of_not_ge fun h ↦ hsS (hT s h)))⟩

end Symmetric

end TauCeti.WeakDerivStep
