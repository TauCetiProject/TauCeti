/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.CantorFunction
public import TauCeti.Analysis.BoundedVariation.OneDimensional.Comparison
public import TauCeti.Analysis.BoundedVariation.Space
import TauCeti.MeasureTheory.VectorMeasure.BoundedVariation
import TauCeti.MeasureTheory.VectorMeasure.ScalarIntegral

/-!
# The singular distributional derivative of the Cantor function

The classical derivative measure of the Cantor–Lebesgue function is the Cantor probability
measure, viewed as a signed measure. Its distributional variation on every open set is
exactly the Cantor measure of that set. Thus its derivative vanishes Lebesgue-almost
everywhere but its distributional variation is one, concentrated on the Cantor set and
without atoms.

The integration-by-parts identity identifies the measure as the distributional derivative,
not merely as an unrelated Stieltjes measure. The function is BV on every open
domain of finite Lebesgue measure; no integrability on the whole line is asserted, since it
is one on `[1, ∞)`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 (classical and distributional variation in one dimension).
-/

public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace TauCeti

/-- The derivative vector measure of the Cantor function is the Cantor probability measure
viewed as a signed measure. -/
theorem vectorMeasure_cantorFunction :
    boundedVariationOn_cantorFunction.vectorMeasure =
      cantorStieltjesFunction.measure.toSignedMeasure := by
  have hf : BoundedVariationOn cantorStieltjesFunction univ := by
    simpa only [coe_cantorStieltjesFunction] using boundedVariationOn_cantorFunction
  simpa only [coe_cantorStieltjesFunction] using
    cantorStieltjesFunction.vectorMeasure_eq_toSignedMeasure hf

/-- Integration by parts for the Cantor function: its distributional derivative is the
Cantor measure. The test function need only be `C¹` and compactly supported. -/
theorem integral_deriv_mul_cantorFunction {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcφ : HasCompactSupport φ) :
    ∫ x, deriv φ x * cantorFunction x = -∫ x, φ x ∂cantorStieltjesFunction.measure := by
  have h := boundedVariationOn_cantorFunction.integral_deriv_smul_eq_neg_integral_vectorMeasure
    hφ hcφ
  have hB : ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) = ContinuousLinearMap.mul ℝ ℝ := by
    ext
    simp
  rw [vectorMeasure_cantorFunction, hB, VectorMeasure.integral_mul_toSignedMeasure] at h
  simpa only [smul_eq_mul] using h

/-- Distributional variation of the Cantor function on any open domain is the Cantor measure
of that domain. This also holds for unbounded domains. -/
theorem totalVariationOn_cantorFunction (Ω : Opens ℝ) :
    totalVariationOn volume Ω cantorFunction = cantorStieltjesFunction.measure Ω := by
  rw [boundedVariationOn_cantorFunction.totalVariationOn_eq_variation_vectorMeasure,
    vectorMeasure_cantorFunction, Measure.variation_toSignedMeasure]

/-- On any open domain the variation measure of the Cantor function is the pullback of the
Cantor measure along the subtype inclusion. -/
theorem variationMeasure_cantorFunction (Ω : Opens ℝ) :
    variationMeasure volume Ω cantorFunction =
      cantorStieltjesFunction.measure.comap ((↑) : Ω → ℝ) := by
  rw [boundedVariationOn_cantorFunction.variationMeasure_eq_comap_variation_vectorMeasure,
    vectorMeasure_cantorFunction, Measure.variation_toSignedMeasure]

/-- The variation measure of the Cantor function on a subset of its domain is the Cantor
measure of its image in the line. -/
theorem variationMeasure_cantorFunction_apply (Ω : Opens ℝ) (s : Set Ω) :
    variationMeasure volume Ω cantorFunction s =
      cantorStieltjesFunction.measure (Subtype.val '' s) := by
  rw [boundedVariationOn_cantorFunction.variationMeasure_apply, vectorMeasure_cantorFunction,
    Measure.variation_toSignedMeasure]

/-- The distributional variation of the Cantor function has no atoms on any open domain. -/
@[simp]
theorem variationMeasure_cantorFunction_singleton (Ω : Opens ℝ) (x : Ω) :
    variationMeasure volume Ω cantorFunction {x} = 0 := by
  rw [variationMeasure_cantorFunction_apply, image_singleton, measure_singleton]

/-- On any open domain, all the distributional variation of the Cantor function is
concentrated on the Cantor set. -/
theorem variationMeasure_cantorFunction_compl_cantorSet (Ω : Opens ℝ) :
    variationMeasure volume Ω cantorFunction (Subtype.val ⁻¹' cantorSetᶜ) = 0 := by
  rw [variationMeasure_cantorFunction_apply]
  exact measure_mono_null (image_preimage_subset _ _)
    cantorStieltjesFunction_measure_compl_cantorSet

/-- The distributional variation of the Cantor function is singular with respect to
Lebesgue measure on its domain. -/
theorem mutuallySingular_variationMeasure_cantorFunction (Ω : Opens ℝ) :
    variationMeasure volume Ω cantorFunction ⟂ₘ volume.comap ((↑) : Ω → ℝ) := by
  refine ⟨Subtype.val ⁻¹' cantorSetᶜ,
    isClosed_cantorSet.isOpen_compl.measurableSet.preimage measurable_subtype_coe,
    variationMeasure_cantorFunction_compl_cantorSet Ω, ?_⟩
  rw [← preimage_compl, compl_compl]
  -- Fix the inclusion's domain as `Ω`, rather than the subtype of its underlying set.
  have hemb : Topology.IsOpenEmbedding ((↑) : Ω → ℝ) := Ω.isOpen.isOpenEmbedding_subtypeVal
  rw [hemb.measurableEmbedding.comap_apply]
  exact measure_mono_null (image_preimage_subset _ _) volume_cantorSet

/-- The whole-line distributional variation of the Cantor function is one, although its
ordinary derivative is zero almost everywhere. -/
@[simp]
theorem totalVariationOn_top_cantorFunction : totalVariationOn volume ⊤ cantorFunction = 1 := by
  rw [totalVariationOn_cantorFunction]
  exact measure_univ

/-- All the variation lies in the unit interval, whose endpoints carry no atoms. -/
@[simp]
theorem totalVariationOn_Ioo_cantorFunction :
    totalVariationOn volume ⟨Ioo 0 1, isOpen_Ioo⟩ cantorFunction = 1 := by
  rw [totalVariationOn_cantorFunction, Opens.coe_mk, StieltjesFunction.measure_Ioo,
    coe_cantorStieltjesFunction, continuous_cantorFunction.continuousWithinAt.leftLim_eq,
    cantorFunction_one, cantorFunction_zero]
  norm_num

/-- The Cantor function belongs to distributional BV on every open domain of finite
Lebesgue measure. In particular this applies to every bounded open domain. -/
theorem memBV_cantorFunction (Ω : Opens ℝ) (hΩ : volume (Ω : Set ℝ) < ∞) :
    MemBV volume Ω cantorFunction := by
  refine memBV_iff.mpr ⟨?_, ?_⟩
  · exact IntegrableOn.of_bound hΩ
      measurable_cantorFunction.aestronglyMeasurable.restrict 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (cantorFunction_nonneg x)]
        exact cantorFunction_le_one x)
  · rw [totalVariationOn_cantorFunction]
    exact measure_lt_top _ _

end TauCeti
