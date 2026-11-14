/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# The point-mass Hilbert basis of counting-measure `L²`

For any measurable space `α` with measurable singletons and `𝕜` satisfying `RCLike 𝕜`, the
singleton indicator classes `indicatorConstLp 2 (measurableSet_singleton a) _ 1` form a Hilbert
basis `MeasureTheory.L2.countHilbertBasis 𝕜 α` of `Lp 𝕜 2 (Measure.count : Measure α)`. No
countability of `α` is assumed: every `L²` class for the counting measure has countable support,
its coordinate at `a` is its pointwise value `f a`, and Parseval's identity holds as an
unconditional sum over `α`.

## Main definitions

* `MeasureTheory.L2.countHilbertBasis 𝕜 α`: the singleton-indicator `HilbertBasis` of
  `Lp 𝕜 2 (Measure.count : Measure α)`.

## Main results

* `MeasureTheory.L2.inner_countHilbertBasis_left`, `MeasureTheory.L2.countHilbertBasis_repr_apply`:
  the inner product `⟪countHilbertBasis 𝕜 α a, f⟫_𝕜` and `a`-th coordinate of `f` equal `f a`.
* `MeasureTheory.L2.hasSum_countHilbertBasis`: `f` is the unconditional `L²`-sum
  `∑' a, f a • countHilbertBasis 𝕜 α a`.
* `MeasureTheory.L2.summable_norm_sq_apply`, `MeasureTheory.L2.norm_sq_eq_tsum_apply`,
  `MeasureTheory.L2.hasSum_conj_mul_apply`: square-summability of values and Parseval's identity.
-/

public section

open scoped ComplexConjugate ENNReal InnerProductSpace

namespace MeasureTheory.L2

variable {𝕜 α : Type*} [RCLike 𝕜] [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The singleton indicators of value `1` are orthonormal in counting-measure `L²`. -/
theorem orthonormal_indicatorConstLp_singleton :
    Orthonormal 𝕜 fun a : α =>
      (indicatorConstLp 2 (measurableSet_singleton a) (by simp) 1 :
        Lp 𝕜 2 (Measure.count : Measure α)) := by
  classical
  refine orthonormal_iff_ite.2 fun a b => ?_
  rw [L2.inner_indicatorConstLp_one_indicatorConstLp_one (measurableSet_singleton a)
    (measurableSet_singleton b) (by simp) (by simp)]
  by_cases hab : a = b
  · subst hab
    simp
  · have hmem : a ∉ ({b} : Set α) := hab
    simp [Set.singleton_inter_eq_empty.2 hmem, hab]

private theorem orthogonal_span_indicatorConstLp_singleton_eq_bot :
    (Submodule.span 𝕜 (Set.range fun a : α =>
      (indicatorConstLp 2 (measurableSet_singleton a) (by simp) 1 :
        Lp 𝕜 2 (Measure.count : Measure α))))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun f hf => ?_
  refine Lp.eq_zero_of_inner_indicatorConstLp_singleton (𝕜 := 𝕜) f fun a c => ?_
  have h1 : ⟪(indicatorConstLp 2 (measurableSet_singleton a) (by simp) 1 :
      Lp 𝕜 2 (Measure.count : Measure α)), f⟫_𝕜 = 0 :=
    (Submodule.mem_orthogonal _ f).1 hf _ (Submodule.subset_span ⟨a, rfl⟩)
  have hc : indicatorConstLp 2 (measurableSet_singleton a)
      (by simp : (Measure.count : Measure α) {a} ≠ ∞) c =
      c • indicatorConstLp 2 (measurableSet_singleton a) (by simp) (1 : 𝕜) := by
    simpa only [smul_eq_mul, mul_one] using
      TauCeti.indicatorConstLp_smul (p := 2) (μ := (Measure.count : Measure α))
        (measurableSet_singleton a) (by simp) c (1 : 𝕜)
  rw [hc, inner_smul_left, h1, mul_zero]

variable (𝕜 α) in
/-- **The point-mass Hilbert basis** of `Lp 𝕜 2 (Measure.count : Measure α)`, sending `a : α` to
the indicator class of `{a}` with value `1`. No countability of `α` is needed. -/
noncomputable def countHilbertBasis :
    HilbertBasis α 𝕜 (Lp 𝕜 2 (Measure.count : Measure α)) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_indicatorConstLp_singleton
    orthogonal_span_indicatorConstLp_singleton_eq_bot

/-- Coercion of `countHilbertBasis 𝕜 α` to the family of unit singleton indicators in `L²`. -/
theorem coe_countHilbertBasis :
    ⇑(countHilbertBasis 𝕜 α) = fun a : α =>
      indicatorConstLp 2 (measurableSet_singleton a)
        (by simp : (Measure.count : Measure α) {a} ≠ ∞) (1 : 𝕜) :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- The `a`-th basis vector of `countHilbertBasis 𝕜 α` is `indicatorConstLp 2 {a} 1`. -/
theorem countHilbertBasis_apply (a : α) :
    countHilbertBasis 𝕜 α a =
      indicatorConstLp 2 (measurableSet_singleton a)
        (by simp : (Measure.count : Measure α) {a} ≠ ∞) (1 : 𝕜) :=
  congrFun coe_countHilbertBasis a

/-- Pointwise values of the `a`-th point-mass basis vector on `α`. -/
theorem coeFn_countHilbertBasis (a x : α) :
    (countHilbertBasis 𝕜 α a : α → 𝕜) x = ({a} : Set α).indicator 1 x := by
  rw [countHilbertBasis_apply]
  exact Measure.ae_count_iff.1
    (indicatorConstLp_coeFn (p := 2) (μ := (Measure.count : Measure α))
      (hs := measurableSet_singleton a) (hμs := by simp) (c := (1 : 𝕜))) x

@[simp]
theorem norm_countHilbertBasis (a : α) : ‖countHilbertBasis 𝕜 α a‖ = 1 :=
  (countHilbertBasis 𝕜 α).orthonormal.1 a

/-- Pairing on the left with the `a`-th point mass evaluates an `L²` function at `a`. -/
@[simp]
theorem inner_countHilbertBasis_left (f : Lp 𝕜 2 (Measure.count : Measure α)) (a : α) :
    ⟪countHilbertBasis 𝕜 α a, f⟫_𝕜 = f a := by
  rw [countHilbertBasis_apply, L2.inner_indicatorConstLp_eq_setIntegral_inner, integral_singleton]
  simp

/-- Pairing on the right with the `a`-th point mass gives the conjugate value at `a`. -/
@[simp]
theorem inner_countHilbertBasis_right (f : Lp 𝕜 2 (Measure.count : Measure α)) (a : α) :
    ⟪f, countHilbertBasis 𝕜 α a⟫_𝕜 = conj (f a) := by
  rw [← inner_conj_symm, inner_countHilbertBasis_left]

@[simp]
theorem countHilbertBasis_repr_apply (f : Lp 𝕜 2 (Measure.count : Measure α)) (a : α) :
    (countHilbertBasis 𝕜 α).repr f a = f a := by
  rw [HilbertBasis.repr_apply_apply, inner_countHilbertBasis_left]

/-- Every `f ∈ L²(count)` is the unconditional `L²`-sum of its values against point masses. -/
theorem hasSum_countHilbertBasis (f : Lp 𝕜 2 (Measure.count : Measure α)) :
    HasSum (fun a : α => f a • countHilbertBasis 𝕜 α a) f := by
  simpa only [countHilbertBasis_repr_apply] using (countHilbertBasis 𝕜 α).hasSum_repr f

/-- The squared norms of the values of any counting-measure `L²` function are summable. -/
theorem summable_norm_sq_apply (f : Lp 𝕜 2 (Measure.count : Measure α)) :
    Summable fun a : α => ‖f a‖ ^ 2 := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have h := (lp.memℓp ((countHilbertBasis 𝕜 α).repr f)).summable hp
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, countHilbertBasis_repr_apply] using h

/-- **Parseval's norm identity** on counting-measure `L²`, with no countability assumption. -/
theorem norm_sq_eq_tsum_apply (f : Lp 𝕜 2 (Measure.count : Measure α)) :
    ‖f‖ ^ 2 = ∑' a : α, ‖f a‖ ^ 2 := by
  have hnorm : ‖f‖ = ‖(countHilbertBasis 𝕜 α).repr f‖ :=
    ((countHilbertBasis 𝕜 α).repr.norm_map f).symm
  rw [hnorm, lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div, countHilbertBasis_repr_apply]
  rw [← Real.rpow_natCast _ 2, Nat.cast_ofNat,
    Real.rpow_inv_rpow (tsum_nonneg fun _ => sq_nonneg _) two_ne_zero]

/-- **Polarized Parseval identity** (`HasSum` form) on counting-measure `L²`. -/
theorem hasSum_conj_mul_apply (f g : Lp 𝕜 2 (Measure.count : Measure α)) :
    HasSum (fun a : α => conj (f a) * g a) ⟪f, g⟫_𝕜 := by
  simpa only [inner_countHilbertBasis_right, inner_countHilbertBasis_left] using
    (countHilbertBasis 𝕜 α).hasSum_inner_mul_inner f g

/-- **Polarized Parseval identity** (`tsum` form) on counting-measure `L²`. -/
theorem tsum_conj_mul_apply (f g : Lp 𝕜 2 (Measure.count : Measure α)) :
    ∑' a : α, conj (f a) * g a = ⟪f, g⟫_𝕜 :=
  (hasSum_conj_mul_apply f g).tsum_eq

end MeasureTheory.L2
