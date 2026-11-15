/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AreaFormula.Basic
import TauCeti.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Weighted area integration on injective regular parametrizations

For an injective map with injective derivative on a Borel set, pushing forward Lebesgue measure
weighted by the geometric Jacobian gives normalized Hausdorff measure on its image. This yields
weighted area integration and the corresponding Bochner integrability criterion in arbitrary
codimension. No global continuity or differentiability outside the parameter set is required.

The nonnegative formulas allow infinite integrals. The Bochner formula is accompanied by an
integrability equivalence, so finite surface integrals can be verified in parameter coordinates.
These results concern the regular injective case; singular derivatives and multiplicities are
not treated here.

The construction uses `MeasureTheory.lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image`.
The measure transport and integral proofs adapt Mathlib's determinant change of variables in
`Mathlib.MeasureTheory.Function.Jacobian` to rectangular derivatives and `normDet`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.3 (the area formula).
-/

public section

open MeasureTheory Measure Set Function Module
open scoped ENNReal

namespace TauCeti

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
  {f : U → V} {s : Set U}

/-- The restricted parametrization pushes forward the Jacobian-weighted parameter measure to
normalized Hausdorff measure on its image. The subtype formulation requires no measurable
extension of the parametrization outside its domain. -/
theorem restrict_map_withDensity_normDet_fderiv_eq_euclideanHausdorffMeasure
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hinj : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hf : InjOn f s) :
    Measure.map (s.domRestrict f)
        (comap (↑) (volume.withDensity fun x ↦ ENNReal.ofReal (fderiv ℝ f x).normDet)) =
      (μHE[finrank ℝ U]).restrict (f '' s) := by
  have hcont : ContinuousOn f s := fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt
  have he := hcont.measurableEmbedding hs hf
  have hc := MeasurableEmbedding.subtype_coe hs
  apply Measure.ext
  intro t ht
  have hr : MeasurableSet (((↑) : s → U) '' (s.domRestrict f ⁻¹' t)) :=
    hc.measurableSet_image.2 (he.measurable ht)
  rw [Measure.map_apply he.measurable ht,
    comap_apply _ hc.injective (fun _ h ↦ hc.measurableSet_image.2 h) _ (he.measurable ht),
    withDensity_apply _ hr,
    MeasureTheory.lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image hr
      (fun x hx ↦ hd x (Subtype.coe_image_subset s _ hx))
      (fun x hx ↦ hinj x (Subtype.coe_image_subset s _ hx))
      (hf.mono (Subtype.coe_image_subset s _)), Measure.restrict_apply ht]
  congr 1
  ext y
  simp only [mem_image, mem_preimage, domRestrict_apply, mem_inter_iff]
  aesop

/-- Weighted area integration for an injective regular parametrization, with normalized
Hausdorff measure in the target. The weight need not be measurable. -/
theorem lintegral_image_eq_lintegral_normDet_fderiv_mul
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hinj : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hf : InjOn f s) (g : V → ℝ≥0∞) :
    ∫⁻ y in f '' s, g y ∂μHE[finrank ℝ U] =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet * g (f x) := by
  have hcont : ContinuousOn f s := fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt
  rw [← restrict_map_withDensity_normDet_fderiv_eq_euclideanHausdorffMeasure hs hd hinj hf,
    (hcont.measurableEmbedding hs hf).lintegral_map]
  simp only [domRestrict_apply, ← Function.comp_apply (f := g)]
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map, map_comap_subtype_coe hs,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ _ _ hs]
  · rfl
  · exact Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  · exact (ENNReal.measurable_ofReal.comp
      (ContinuousLinearMap.continuous_normDet.measurable.comp (measurable_fderiv ℝ f))).aemeasurable

/-- The weighted injective area formula written with a weight on the parameter space.
The inverse on the image is unambiguous by injectivity on `s`. -/
theorem lintegral_normDet_fderiv_mul_eq_lintegral_invFunOn
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hinj : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hf : InjOn f s) (g : U → ℝ≥0∞) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ f x).normDet * g x =
      ∫⁻ y in f '' s, g (invFunOn f s y) ∂μHE[finrank ℝ U] := by
  rw [lintegral_image_eq_lintegral_normDet_fderiv_mul hs hd hinj hf]
  exact setLIntegral_congr_fun hs fun x hx ↦ by rw [hf.leftInvOn_invFunOn hx]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Surface integrability is equivalent to integrability of the Jacobian-weighted pullback
under an injective regular parametrization. -/
theorem integrableOn_image_iff_integrableOn_normDet_fderiv_smul
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hinj : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hf : InjOn f s) (g : V → F) :
    IntegrableOn g (f '' s) μHE[finrank ℝ U] ↔
      IntegrableOn (fun x ↦ (fderiv ℝ f x).normDet • g (f x)) s := by
  have hcont : ContinuousOn f s := fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt
  rw [IntegrableOn,
    ← restrict_map_withDensity_normDet_fderiv_eq_euclideanHausdorffMeasure hs hd hinj hf,
    (hcont.measurableEmbedding hs hf).integrable_map_iff]
  simp only [domRestrict_eq, ← Function.comp_assoc]
  rw [← (MeasurableEmbedding.subtype_coe hs).integrable_map_iff, map_comap_subtype_coe hs,
    restrict_withDensity hs, integrable_withDensity_iff_integrable_smul₀']
  · simp only [ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _), Function.comp_apply,
      IntegrableOn]
  · exact (ENNReal.measurable_ofReal.comp
      (ContinuousLinearMap.continuous_normDet.measurable.comp (measurable_fderiv ℝ f))).aemeasurable
  · exact Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top

/-- Bochner area integration for an injective regular parametrization. Integrability can be
checked by `integrableOn_image_iff_integrableOn_normDet_fderiv_smul`. -/
theorem integral_image_eq_integral_normDet_fderiv_smul
    (hs : MeasurableSet s) (hd : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hinj : ∀ x ∈ s, Injective (fderiv ℝ f x)) (hf : InjOn f s) (g : V → F) :
    ∫ y in f '' s, g y ∂μHE[finrank ℝ U] =
      ∫ x in s, (fderiv ℝ f x).normDet • g (f x) := by
  have hcont : ContinuousOn f s := fun x hx ↦ (hd x hx).continuousAt.continuousWithinAt
  rw [← restrict_map_withDensity_normDet_fderiv_eq_euclideanHausdorffMeasure hs hd hinj hf,
    (hcont.measurableEmbedding hs hf).integral_map]
  simp only [domRestrict_apply, ← Function.comp_apply (f := g)]
  rw [← (MeasurableEmbedding.subtype_coe hs).integral_map, map_comap_subtype_coe hs,
    setIntegral_withDensity_eq_setIntegral_toReal_smul₀]
  · simp only [ENNReal.toReal_ofReal (LinearMap.normDet_nonneg _)]
  · exact (ENNReal.measurable_ofReal.comp
      (ContinuousLinearMap.continuous_normDet.measurable.comp (measurable_fderiv ℝ f))).aemeasurable
  · exact Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  · exact hs

end TauCeti
