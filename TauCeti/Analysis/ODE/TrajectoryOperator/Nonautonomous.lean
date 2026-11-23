/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain
public import TauCeti.Analysis.Fredholm.ContinuousFamily
public import TauCeti.MeasureTheory.Function.Lp.Operator.LpMultiplication
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The nonautonomous trajectory operator over a common domain

Let `ι : D →L[ℝ] H` embed a Banach space `D` into a Banach space `H`, as a Sobolev domain into
`L²` of a circle or an interval. A path of unbounded operators on `H` with the common domain `D` is
a path `A(s)` of bounded operators `D →L[ℝ] H`. This file realizes the operator `∂s + A(s)` from
`Lᵖ(Ω, D) ∩ W^{1,p}(Ω, H)` to `Lᵖ(Ω, H)`, for an open `Ω ⊆ ℝ` and an essentially bounded,
strongly measurable coefficient `A`, recorded as an element of `L∞(Ω, D →L[ℝ] H)`:

`TauCeti.WeakDerivStep.nonautonomousDomainTrajectoryOperator ι A u = (ι ∘ u)' + A(s) u(s)`.

The domain is the weak-derivative graph `WeakDerivStep mu Omega p (ι.compLpL p μΩ)` of
`TauCeti.Analysis.ODE.TrajectoryOperator.CommonDomain`, whose norm controls `u` in `Lᵖ(Ω, D)` and
the weak derivative of `ι ∘ u` in `Lᵖ(Ω, H)`. The coefficient acts by pointwise operator
application `MeasureTheory.Lp.operatorMultiplication`, which wraps Mathlib's Hölder multiplication
`ContinuousLinearMap.holderL`. For a constant coefficient `A₀` the operator is the
autonomous `TauCeti.WeakDerivStep.domainTrajectoryOperator ι A₀`
(`TauCeti.WeakDerivStep.nonautonomousDomainTrajectoryOperator_toLp_const`).

The operator has norm at most `1 + ‖A‖`, and it depends `1`-Lipschitz continuously on the
coefficient in `L∞`. Solving `(∂s + A) u = f` is the weak equation `(ι ∘ u)' = f - A u`, and every
weak solution `x ∈ Lᵖ(Ω, D)` of that equation lifts to the graph.

On the whole line with `p = 2`, the autonomous operator of an invertible `ι`-symmetric `A₀`
(`⟪A₀ x, ι y⟫ = ⟪ι x, A₀ y⟫`) is invertible with inverse of norm at most `C = √(1 + ‖A₀⁻¹‖²)`.
A coefficient within `δ` of `A₀` almost everywhere, with `C δ < 1`, therefore gives an invertible
operator whose inverse has norm at most `C / (1 - C δ)`
(`TauCeti.WeakDerivStep.isInvertible_nonautonomousDomainTrajectoryOperator_of_ae_norm_sub_le` and
`TauCeti.WeakDerivStep.norm_inverse_nonautonomousDomainTrajectoryOperator_le_of_ae_norm_sub_le`).
This is the estimate on the ends of the line, where a path of self-adjoint operators with
invertible limits `A±` stays close to them; the coefficient itself need not be symmetric there.
Along any affine deformation of the coefficient through Fredholm operators the index is constant
(`TauCeti.WeakDerivStep.index_nonautonomousDomainTrajectoryOperator_eq_of_forall_isFredholm`).

## Main declarations

* `TauCeti.WeakDerivStep.nonautonomousDomainTrajectoryOperator`: the operator `∂s + A(s)`.
* `TauCeti.WeakDerivStep.nonautonomousDomainTrajectoryOperator_apply_ae`: its pointwise formula.
* `TauCeti.WeakDerivStep.nonautonomousDomainTrajectoryOperator_toLp_const`: the constant
  coefficient case.
* `TauCeti.WeakDerivStep.lipschitzWith_nonautonomousDomainTrajectoryOperator`: Lipschitz
  dependence on the coefficient.
* `TauCeti.WeakDerivStep.nonautonomousDomainTrajectoryOperator_eq_iff_hasWeakLineDerivOn`: the
  weak equation.
* `TauCeti.WeakDerivStep.isInvertible_nonautonomousDomainTrajectoryOperator_of_ae_norm_sub_le`:
  invertibility near an invertible `ι`-symmetric constant.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1–33, §§3–4 (the operator `d/ds + A(s)` for paths of unbounded self-adjoint
  operators with a common domain).
* D. Salamon, *Lectures on Floer homology*, IAS/Park City Math. Ser. **7** (1999), Lecture 2.
-/

public section

noncomputable section

namespace TauCeti.WeakDerivStep

open MeasureTheory TopologicalSpace
open scoped ENNReal InnerProductSpace

section Banach

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
  {mu : Measure ℝ} [IsFiniteMeasureOnCompacts mu] {Omega : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

local notation "μΩ" => (mu.restrict Omega)

/-- The nonautonomous first-order operator `u ↦ (ι ∘ u)' + A(s) u(s)` from
`Lᵖ(Ω, D) ∩ W^{1,p}(Ω, H)` to `Lᵖ(Ω, H)`, for an `L∞` coefficient `A` with values in `D →L[ℝ] H`.
It depends only on the almost everywhere class of the coefficient. -/
def nonautonomousDomainTrajectoryOperator (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ) :
    WeakDerivStep mu Omega p (ι.compLpL p μΩ) →L[ℝ] Lp H p μΩ :=
  ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ).comp (weakFDerivL (ι.compLpL p μΩ)) +
    (Lp.operatorMultiplication p A).comp (prevL (ι.compLpL p μΩ))

/-- Unfolding formula for `nonautonomousDomainTrajectoryOperator`. -/
theorem nonautonomousDomainTrajectoryOperator_def (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ) :
    nonautonomousDomainTrajectoryOperator (p := p) ι A =
      ((ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ).comp (weakFDerivL (ι.compLpL p μΩ)) +
        (Lp.operatorMultiplication p A).comp (prevL (ι.compLpL p μΩ)) := (rfl)

/-- The operator adds the weak derivative in direction `1` to the coefficient action. -/
@[simp] theorem nonautonomousDomainTrajectoryOperator_apply (ι : D →L[ℝ] H)
    (A : Lp (D →L[ℝ] H) ∞ μΩ) (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) :
    nonautonomousDomainTrajectoryOperator ι A u =
      (ContinuousLinearMap.apply ℝ H (1 : ℝ)).compLpL p μΩ (weakFDeriv (ι.compLpL p μΩ) u) +
        Lp.operatorMultiplication p A (prev (ι.compLpL p μΩ) u) := by
  simp [nonautonomousDomainTrajectoryOperator]

/-- Pointwise almost-everywhere formula: `(∂s + A) u (s) = (ι ∘ u)'(s) + A(s) u(s)`. -/
theorem nonautonomousDomainTrajectoryOperator_apply_ae (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ)
    (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) :
    nonautonomousDomainTrajectoryOperator ι A u =ᵐ[μΩ]
      fun s ↦ weakFDeriv (ι.compLpL p μΩ) u s 1 + A s (prev (ι.compLpL p μΩ) u s) := by
  let base := ι.compLpL p μΩ
  rw [nonautonomousDomainTrajectoryOperator_apply]
  filter_upwards [Lp.coeFn_add _ (Lp.operatorMultiplication p A (prev base u)),
    (ContinuousLinearMap.apply ℝ H (1 : ℝ)).coeFn_compLpL (weakFDeriv base u),
    Lp.operatorMultiplication_ae A (prev base u)] with s hadd hd hA
  rw [hadd, Pi.add_apply, hd, hA, ContinuousLinearMap.apply_apply]

/-- Subtracting two operators cancels the derivative part and leaves multiplication by the
difference of the coefficients. -/
theorem nonautonomousDomainTrajectoryOperator_sub (ι : D →L[ℝ] H) (A B : Lp (D →L[ℝ] H) ∞ μΩ) :
    nonautonomousDomainTrajectoryOperator (p := p) ι A -
        nonautonomousDomainTrajectoryOperator ι B =
      (Lp.operatorMultiplication p (A - B)).comp (prevL (ι.compLpL p μΩ)) := by
  simp only [nonautonomousDomainTrajectoryOperator, map_sub, ContinuousLinearMap.sub_comp]
  abel

/-- The operator norm of `∂s + A` is at most `1 + ‖A‖`. -/
theorem norm_nonautonomousDomainTrajectoryOperator_le (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ) :
    ‖nonautonomousDomainTrajectoryOperator (p := p) ι A‖ ≤ 1 + ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  rw [nonautonomousDomainTrajectoryOperator_apply, one_add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [ContinuousLinearMap.compLpL_apply, ContinuousLinearMap.norm_apply_one_compLp]
    exact norm_weakFDeriv_le _ u
  · exact (Lp.norm_operatorMultiplication_apply_le A _).trans
      (mul_le_mul_of_nonneg_left (norm_prev_le _ u) (norm_nonneg _))

/-- Changing the coefficient from `B` to `A` changes `∂s + A` by at most `‖A - B‖` in norm. -/
theorem norm_nonautonomousDomainTrajectoryOperator_sub_le (ι : D →L[ℝ] H)
    (A B : Lp (D →L[ℝ] H) ∞ μΩ) :
    ‖nonautonomousDomainTrajectoryOperator (p := p) ι A -
      nonautonomousDomainTrajectoryOperator ι B‖ ≤ ‖A - B‖ := by
  rw [nonautonomousDomainTrajectoryOperator_sub]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun u ↦ ?_
  rw [ContinuousLinearMap.comp_apply, prevL_apply]
  exact (Lp.norm_operatorMultiplication_apply_le _ _).trans
    (mul_le_mul_of_nonneg_left (norm_prev_le _ u) (norm_nonneg _))

/-- `∂s + A` depends `1`-Lipschitz continuously on its `L∞` coefficient. -/
theorem lipschitzWith_nonautonomousDomainTrajectoryOperator (ι : D →L[ℝ] H) :
    LipschitzWith 1
      (nonautonomousDomainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι) :=
  LipschitzWith.of_dist_le_mul fun A B ↦ by
    simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using
      norm_nonautonomousDomainTrajectoryOperator_sub_le ι A B

/-- `∂s + A` depends continuously on its `L∞` coefficient. -/
@[fun_prop] theorem continuous_nonautonomousDomainTrajectoryOperator (ι : D →L[ℝ] H) :
    Continuous (nonautonomousDomainTrajectoryOperator (mu := mu) (Omega := Omega) (p := p) ι) :=
  (lipschitzWith_nonautonomousDomainTrajectoryOperator ι).continuous

/-- For the constant coefficient `A₀`, `∂s + A₀` is the autonomous operator
`TauCeti.WeakDerivStep.domainTrajectoryOperator ι A₀`. -/
@[simp] theorem nonautonomousDomainTrajectoryOperator_toLp_const (ι A₀ : D →L[ℝ] H) :
    nonautonomousDomainTrajectoryOperator (p := p) ι
        ((memLp_top_const (μ := μΩ) A₀).toLp fun _ ↦ A₀) =
      domainTrajectoryOperator ι A₀ := by
  rw [nonautonomousDomainTrajectoryOperator_def, domainTrajectoryOperator_def,
    Lp.operatorMultiplication_of_ae_eq_const (memLp_top_const (μ := μΩ) A₀).coeFn_toLp]

/-- The difference between `∂s + A` and the autonomous `∂s + A₀` is at most `δ` in norm when
`‖A(s) - A₀‖ ≤ δ` for almost every `s`. -/
theorem norm_nonautonomousDomainTrajectoryOperator_sub_domainTrajectoryOperator_le
    (ι A₀ : D →L[ℝ] H) {A : Lp (D →L[ℝ] H) ∞ μΩ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hA : ∀ᵐ s ∂μΩ, ‖A s - A₀‖ ≤ δ) :
    ‖nonautonomousDomainTrajectoryOperator (p := p) ι A - domainTrajectoryOperator ι A₀‖ ≤ δ := by
  let A₀L := (memLp_top_const (μ := μΩ) A₀).toLp fun _ ↦ A₀
  rw [← nonautonomousDomainTrajectoryOperator_toLp_const ι A₀]
  refine (norm_nonautonomousDomainTrajectoryOperator_sub_le ι A A₀L).trans
    (Lp.norm_le_of_ae_bound_top hδ ?_)
  filter_upwards [Lp.coeFn_sub A A₀L, (memLp_top_const (μ := μΩ) A₀).coeFn_toLp, hA]
    with s hsub hA₀ hs
  rwa [hsub, Pi.sub_apply, hA₀]

/-- Solving `(∂s + A) u = f` is the weak equation `(ι ∘ u)' = f - A u`. -/
theorem nonautonomousDomainTrajectoryOperator_eq_iff_hasWeakLineDerivOn (ι : D →L[ℝ] H)
    (A : Lp (D →L[ℝ] H) ∞ μΩ) (u : WeakDerivStep mu Omega p (ι.compLpL p μΩ)) (f : Lp H p μΩ) :
    nonautonomousDomainTrajectoryOperator ι A u = f ↔ HasWeakLineDerivOn mu Omega
      (ι.compLpL p μΩ (prev (ι.compLpL p μΩ) u))
      (fun s ↦ f s - A s (prev (ι.compLpL p μΩ) u s)) 1 := by
  have hd := (hasWeakFDerivOn_base_prev (ι.compLpL p μΩ) u).hasWeakLineDerivOn 1
  refine ⟨fun h ↦ hd.congr_ae_deriv ?_, fun h ↦ Lp.ext ?_⟩
  · filter_upwards [h ▸ nonautonomousDomainTrajectoryOperator_apply_ae ι A u] with s hs
    exact eq_sub_iff_add_eq.mpr hs.symm
  · filter_upwards [nonautonomousDomainTrajectoryOperator_apply_ae ι A u, hd.ae_eq h] with s hs hd'
    rw [hs, hd', sub_add_cancel]

/-- **Weak solutions lift to the graph.** If `x ∈ Lᵖ(Ω, D)` solves `(ι ∘ x)' = f - A x` weakly on
`Ω`, then `x` is the value of a graph element `u` with `(∂s + A) u = f`. -/
theorem exists_prev_eq_and_nonautonomousDomainTrajectoryOperator_eq_of_hasWeakLineDerivOn
    (ι : D →L[ℝ] H) (A : Lp (D →L[ℝ] H) ∞ μΩ) {x : Lp D p μΩ} {f : Lp H p μΩ}
    (h : HasWeakLineDerivOn mu Omega (ι.compLpL p μΩ x) (fun s ↦ f s - A s (x s)) 1) :
    ∃ u : WeakDerivStep mu Omega p (ι.compLpL p μΩ),
      prev (ι.compLpL p μΩ) u = x ∧ nonautonomousDomainTrajectoryOperator ι A u = f := by
  let g := f - Lp.operatorMultiplication p A x
  have hg : (fun s ↦ f s - A s (x s)) =ᵐ[μΩ] g := by
    filter_upwards [Lp.coeFn_sub f (Lp.operatorMultiplication p A x),
      Lp.operatorMultiplication_ae A x] with s hs hA
    simp only [g, hs, Pi.sub_apply, hA]
  refine ⟨mkLine _ x g (h.congr_ae_deriv hg), prev_mkLine _ _ _ _, ?_⟩
  rwa [nonautonomousDomainTrajectoryOperator_eq_iff_hasWeakLineDerivOn, prev_mkLine]

/-- **Homotopy invariance of the index.** If `∂s + ((1 - t) A + t B)` is Fredholm for every
`t ∈ [0, 1]`, then `∂s + A` and `∂s + B` have the same index. -/
theorem index_nonautonomousDomainTrajectoryOperator_eq_of_forall_isFredholm [CompleteSpace D]
    (ι : D →L[ℝ] H) {A B : Lp (D →L[ℝ] H) ∞ μΩ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (nonautonomousDomainTrajectoryOperator (p := p) ι ((1 - t) • A + t • B)).IsFredholm) :
    (nonautonomousDomainTrajectoryOperator (p := p) ι A).index =
      (nonautonomousDomainTrajectoryOperator (p := p) ι B).index := by
  have hcont : Continuous fun t : ℝ ↦
      nonautonomousDomainTrajectoryOperator (p := p) ι ((1 - t) • A + t • B) :=
    (continuous_nonautonomousDomainTrajectoryOperator ι).comp (by fun_prop)
  simpa using hcont.continuousOn.index_eq_of_isPreconnected h isPreconnected_Icc
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)

end Banach

section NearConstant

local notation "μ₀" => (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))

variable {D H : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [CompleteSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {ι A₀ : D →L[ℝ] H}
  {A : Lp (D →L[ℝ] H) ∞ μ₀} {δ : ℝ}

omit [CompleteSpace D] [CompleteSpace H] in
/-- An almost-everywhere bound on the line is nonnegative, since Lebesgue measure is nonzero. -/
private theorem nonneg_of_ae_norm_sub_le (hA : ∀ᵐ s ∂μ₀, ‖A s - A₀‖ ≤ δ) : 0 ≤ δ := by
  have hA' : ∀ᵐ s ∂(volume : Measure ℝ), ‖A s - A₀‖ ≤ δ := by simpa using hA
  obtain ⟨s, hs⟩ := hA'.exists
  exact (norm_nonneg _).trans hs

/-- **Invertibility near an invertible symmetric constant.** On `L²(ℝ)`, let `A₀` be invertible
and `ι`-symmetric, and let `‖A(s) - A₀‖ ≤ δ` for almost every `s`, with
`√(1 + ‖A₀⁻¹‖²) δ < 1`. Then `∂s + A` is invertible. -/
theorem isInvertible_nonautonomousDomainTrajectoryOperator_of_ae_norm_sub_le
    (hSymm : ∀ x y : D, ⟪A₀ x, ι y⟫_ℝ = ⟪ι x, A₀ y⟫_ℝ) (hA₀ : A₀.IsInvertible)
    (hA : ∀ᵐ s ∂μ₀, ‖A s - A₀‖ ≤ δ) (hsmall : √(1 + ‖A₀.inverse‖ ^ 2) * δ < 1) :
    (nonautonomousDomainTrajectoryOperator (p := 2) ι A).IsInvertible :=
  (isInvertible_domainTrajectoryOperator hSymm hA₀).of_mul_norm_sub_lt
    (norm_inverse_domainTrajectoryOperator_le hSymm hA₀)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (norm_nonautonomousDomainTrajectoryOperator_sub_domainTrajectoryOperator_le ι A₀
        (nonneg_of_ae_norm_sub_le hA) hA)
      (Real.sqrt_nonneg _)) hsmall)

/-- **The inverse bound near an invertible symmetric constant.** Under the hypotheses of
`isInvertible_nonautonomousDomainTrajectoryOperator_of_ae_norm_sub_le`, with
`C = √(1 + ‖A₀⁻¹‖²)`, the inverse of `∂s + A` has norm at most `C / (1 - C δ)`. -/
theorem norm_inverse_nonautonomousDomainTrajectoryOperator_le_of_ae_norm_sub_le
    (hSymm : ∀ x y : D, ⟪A₀ x, ι y⟫_ℝ = ⟪ι x, A₀ y⟫_ℝ) (hA₀ : A₀.IsInvertible)
    (hA : ∀ᵐ s ∂μ₀, ‖A s - A₀‖ ≤ δ) (hsmall : √(1 + ‖A₀.inverse‖ ^ 2) * δ < 1) :
    ‖(nonautonomousDomainTrajectoryOperator (p := 2) ι A).inverse‖ ≤
      √(1 + ‖A₀.inverse‖ ^ 2) / (1 - √(1 + ‖A₀.inverse‖ ^ 2) * δ) := by
  set C := √(1 + ‖A₀.inverse‖ ^ 2)
  have hdiff := norm_nonautonomousDomainTrajectoryOperator_sub_domainTrajectoryOperator_le
    (p := 2) ι A₀ (nonneg_of_ae_norm_sub_le hA) hA
  have hCδ : C * ‖nonautonomousDomainTrajectoryOperator (p := 2) ι A -
      domainTrajectoryOperator ι A₀‖ ≤ C * δ :=
    mul_le_mul_of_nonneg_left hdiff (Real.sqrt_nonneg _)
  refine ((isInvertible_domainTrajectoryOperator hSymm hA₀).norm_inverse_le_of_mul_norm_sub_lt
    (norm_inverse_domainTrajectoryOperator_le hSymm hA₀) (hCδ.trans_lt hsmall)).trans ?_
  gcongr

/-- Under the hypotheses of
`isInvertible_nonautonomousDomainTrajectoryOperator_of_ae_norm_sub_le`, `∂s + A` is Fredholm. -/
theorem isFredholm_nonautonomousDomainTrajectoryOperator_of_ae_norm_sub_le
    (hSymm : ∀ x y : D, ⟪A₀ x, ι y⟫_ℝ = ⟪ι x, A₀ y⟫_ℝ) (hA₀ : A₀.IsInvertible)
    (hA : ∀ᵐ s ∂μ₀, ‖A s - A₀‖ ≤ δ) (hsmall : √(1 + ‖A₀.inverse‖ ^ 2) * δ < 1) :
    (nonautonomousDomainTrajectoryOperator (p := 2) ι A).IsFredholm :=
  (isInvertible_nonautonomousDomainTrajectoryOperator_of_ae_norm_sub_le hSymm hA₀ hA
    hsmall).isFredholm

/-- Under the hypotheses of
`isInvertible_nonautonomousDomainTrajectoryOperator_of_ae_norm_sub_le`, `∂s + A` has index `0`. -/
theorem index_nonautonomousDomainTrajectoryOperator_of_ae_norm_sub_le
    (hSymm : ∀ x y : D, ⟪A₀ x, ι y⟫_ℝ = ⟪ι x, A₀ y⟫_ℝ) (hA₀ : A₀.IsInvertible)
    (hA : ∀ᵐ s ∂μ₀, ‖A s - A₀‖ ≤ δ) (hsmall : √(1 + ‖A₀.inverse‖ ^ 2) * δ < 1) :
    (nonautonomousDomainTrajectoryOperator (p := 2) ι A).index = 0 :=
  ContinuousLinearMap.index_eq_zero_of_bijective _
    (isInvertible_nonautonomousDomainTrajectoryOperator_of_ae_norm_sub_le hSymm hA₀ hA
      hsmall).bijective

end NearConstant

end TauCeti.WeakDerivStep
