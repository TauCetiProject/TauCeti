/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.L2Space.Basic
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The point-mass Hilbert basis and Parseval identities on counting-measure `L²`

Counting-measure `L²(α)` supplies the Hilbert space of discrete harmonic analysis and group von
Neumann algebras `L(Γ)`, where Fourier expansions, convolution formulas, and trace calculations
rely on the point-mass orthonormal basis and unconditional Parseval sums without countability
hypotheses.

When singletons are measurable (`[MeasurableSingletonClass α]`), the unit singleton indicators form
a Hilbert basis `MeasureTheory.L2.countHilbertBasis 𝕜 α` whose coordinates are pointwise values
(`MeasureTheory.L2.inner_countHilbertBasis_left`, `MeasureTheory.L2.countHilbertBasis_repr_apply`,
`MeasureTheory.L2.hasSum_countHilbertBasis`). On any measurable space `α` (without measurable
singletons), every vector-valued `f : Lp E 2 (Measure.count : Measure α)` satisfies the
unconditional norm-square and polarized Parseval identities
(`MeasureTheory.L2.hasSum_norm_sq_apply`, `MeasureTheory.L2.norm_sq_eq_tsum_apply`,
`MeasureTheory.L2.hasSum_inner_apply`, `MeasureTheory.L2.hasSum_conj_mul_apply`).
-/

public section

open scoped ComplexConjugate ENNReal InnerProductSpace

namespace MeasureTheory.L2

section Basis

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
  · subst hab; simp
  · simp [Set.singleton_inter_eq_empty.2 (Set.notMem_singleton_iff.2 hab), hab]

private theorem orthogonal_span_indicatorConstLp_singleton_eq_bot :
    (Submodule.span 𝕜 (Set.range fun a : α =>
      (indicatorConstLp 2 (measurableSet_singleton a) (by simp) 1 :
        Lp 𝕜 2 (Measure.count : Measure α))))ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun f hf =>
    Lp.eq_zero_of_inner_indicatorConstLp_singleton (𝕜 := 𝕜) f fun a c => ?_
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

/-- Representative function of the `a`-th point-mass basis vector on `α`. -/
@[simp]
theorem coeFn_countHilbertBasis (a : α) :
    (countHilbertBasis 𝕜 α a : α → 𝕜) = ({a} : Set α).indicator 1 :=
  funext fun x => by
    rw [countHilbertBasis_apply]
    exact Measure.ae_count_iff.1 (indicatorConstLp_coeFn (p := 2)
      (μ := (Measure.count : Measure α)) (hs := measurableSet_singleton a) (hμs := by simp)
      (c := (1 : 𝕜))) x

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

/-- The `a`-th Hilbert-basis coordinate of `f ∈ L²(count)` is its pointwise value `f a`. -/
@[simp]
theorem countHilbertBasis_repr_apply (f : Lp 𝕜 2 (Measure.count : Measure α)) (a : α) :
    (countHilbertBasis 𝕜 α).repr f a = f a := by
  rw [HilbertBasis.repr_apply_apply, inner_countHilbertBasis_left]

/-- Every `f ∈ L²(count)` is the unconditional `L²`-sum of its values against point masses. -/
theorem hasSum_countHilbertBasis (f : Lp 𝕜 2 (Measure.count : Measure α)) :
    HasSum (fun a : α => f a • countHilbertBasis 𝕜 α a) f := by
  simpa only [countHilbertBasis_repr_apply] using (countHilbertBasis 𝕜 α).hasSum_repr f

end Basis

section NormSq

variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]

/-- **Parseval's norm identity** (`HasSum` form) on counting-measure `L²`, with no countability or
measurable-singleton assumption. -/
theorem hasSum_norm_sq_apply (f : Lp E 2 (Measure.count : Measure α)) :
    HasSum (fun a : α => ‖f a‖ ^ 2) (‖f‖ ^ 2) := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  exact hasSum_integral_count
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f))

/-- The squared norms of the values of any counting-measure `L²` function are summable. -/
theorem summable_norm_sq_apply (f : Lp E 2 (Measure.count : Measure α)) :
    Summable fun a : α => ‖f a‖ ^ 2 :=
  (hasSum_norm_sq_apply f).summable

/-- **Parseval's norm identity** (`tsum` form) on counting-measure `L²`, with no countability or
measurable-singleton assumption. -/
theorem norm_sq_eq_tsum_apply (f : Lp E 2 (Measure.count : Measure α)) :
    ‖f‖ ^ 2 = ∑' a : α, ‖f a‖ ^ 2 :=
  (hasSum_norm_sq_apply f).tsum_eq.symm

end NormSq

section Polarized

variable {𝕜 α E : Type*} [RCLike 𝕜] [MeasurableSpace α] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- **Polarized Parseval identity** (`HasSum` form) for vector-valued counting-measure `L²`. -/
theorem hasSum_inner_apply (f g : Lp E 2 (Measure.count : Measure α)) :
    HasSum (fun a : α => ⟪f a, g a⟫_𝕜) ⟪f, g⟫_𝕜 := by
  rw [L2.inner_def]
  exact hasSum_integral_count (L2.integrable_inner f g)

/-- **Polarized Parseval identity** (`tsum` form) for vector-valued counting-measure `L²`. -/
theorem tsum_inner_apply (f g : Lp E 2 (Measure.count : Measure α)) :
    ∑' a : α, ⟪f a, g a⟫_𝕜 = ⟪f, g⟫_𝕜 :=
  (hasSum_inner_apply f g).tsum_eq

/-- **Polarized Parseval identity** (`HasSum` form) on scalar counting-measure `L²`. -/
theorem hasSum_conj_mul_apply (f g : Lp 𝕜 2 (Measure.count : Measure α)) :
    HasSum (fun a : α => conj (f a) * g a) ⟪f, g⟫_𝕜 :=
  (hasSum_inner_apply f g).congr_fun fun a => by rw [RCLike.inner_apply, mul_comm]

/-- **Polarized Parseval identity** (`tsum` form) on scalar counting-measure `L²`. -/
theorem tsum_conj_mul_apply (f g : Lp 𝕜 2 (Measure.count : Measure α)) :
    ∑' a : α, conj (f a) * g a = ⟪f, g⟫_𝕜 :=
  (hasSum_conj_mul_apply f g).tsum_eq

end Polarized

end MeasureTheory.L2
