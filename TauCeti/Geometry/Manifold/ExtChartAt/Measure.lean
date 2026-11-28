/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Data.Set.Restrict
import TauCeti.Geometry.Manifold.ExtChartAt.Measurable
import TauCeti.MeasureTheory.Measure.Subtype

/-!
# Measure pushforwards and pullbacks for extended charts

This file provides elementary measure-theoretic pushforward, pullback, null-set, and
chart-localized measure lemmas for arbitrary extended charts `e.extend I`, without smoothness or
Jacobian dependencies.

## Main definitions

* `OpenPartialHomeomorph.localChartMeasure`: pull a weighted measure on the model space back along
  an extended chart `e.extend I` to a measure supported on `e.source`.

## Main results

* `OpenPartialHomeomorph.map_restrict_extend_apply`: evaluation of `(μ.restrict e.source).map
  (e.extend I)` on a measurable set.
* `OpenPartialHomeomorph.map_restrict_extend_apply_image`: `(μ.restrict e.source).map (e.extend I)`
  gives the coordinate image of any subset of `e.source` the measure `μ` gives the subset.
* `OpenPartialHomeomorph.setLIntegral_eq_setLIntegral_map_extend`: lower integrals over a subset
  of `e.source` are lower integrals in `e.extend I` against `(μ.restrict e.source).map
  (e.extend I)`, with no measurability assumption.
* `OpenPartialHomeomorph.setLIntegral_eq_of_map_restrict_eq`: converting a chart pushforward
  `withDensity` identity into a coordinate Lebesgue integral over measurable subsets of `e.source`.
* `OpenPartialHomeomorph.measure_eq_zero_iff_image_extend_of_map_restrict_eq`: a subset of
  `e.source` has `μ`-measure zero iff its extended-chart image has `ν`-measure zero when `μ` has
  an a.e.-nonzero `ℝ≥0∞`-valued chart density.
* `OpenPartialHomeomorph.restrict_source_localChartMeasure`,
  `OpenPartialHomeomorph.localChartMeasure_apply_compl_source`,
  `OpenPartialHomeomorph.map_localChartMeasure_extend`,
  `OpenPartialHomeomorph.localChartMeasure_apply`,
  `OpenPartialHomeomorph.setLIntegral_localChartMeasure`, and
  `OpenPartialHomeomorph.setIntegral_localChartMeasure`: support, same-chart pushforward,
  evaluation, and coordinate integration for `OpenPartialHomeomorph.localChartMeasure`.
-/

public section

open MeasureTheory Set
open scoped ENNReal Manifold Topology

noncomputable section

namespace OpenPartialHomeomorph

section ExtendMeasure

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M]

/-- Evaluation of the pushforward of a measure restricted to a chart source along the
extended chart `e.extend I`. -/
theorem map_restrict_extend_apply [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [OpensMeasurableSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (μ : Measure M) {A : Set E} (hA : MeasurableSet A) :
    ((μ.restrict e.source).map (e.extend I)) A = μ (e.extend I ⁻¹' A ∩ e.source) := by
  rw [Measure.map_apply_of_aemeasurable
      (ContinuousOn.aemeasurable
        ((e.continuousOn_extend (I := I)).mono (e.extend_source (I := I)).ge)
        e.open_source.measurableSet) hA,
    Measure.restrict_apply' e.open_source.measurableSet]

/-- Pushing `μ.restrict e.source` forward along `e.extend I` gives the coordinate image of any
(not necessarily measurable) subset `s ⊆ e.source` the measure `μ s`. -/
theorem map_restrict_extend_apply_image [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (μ : Measure M) {s : Set M} (hsub : s ⊆ e.source) :
    ((μ.restrict e.source).map (e.extend I)) (e.extend I '' s) = μ s := by
  have hsrc : MeasurableSet e.source := e.open_source.measurableSet
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) := .subtypeVal hsrc
  have hae : AEMeasurable (e.extend I) (μ.restrict e.source) :=
    ContinuousOn.aemeasurable
      ((e.continuousOn_extend (I := I)).mono (e.extend_source (I := I)).ge) hsrc
  rw [Measure.map_restrict_eq_map_comap_subtypeVal hsrc μ hae, hR.map_apply,
    ((e.extend I).injOn.mono (e.extend_source (I := I)).ge).preimage_domRestrict_image hsub,
    hval.comap_apply, Subtype.image_preimage_coe, inter_eq_right.2 hsub]

/-- **Integration in an extended chart.** Over a subset `s` of `e.source`, the lower integral of
`f` against `μ` is the lower integral, over `e.extend I '' s`, of `f ∘ (e.extend I).symm` against
`(μ.restrict e.source).map (e.extend I)`. No measurability of `s` or `f` is needed. -/
theorem setLIntegral_eq_setLIntegral_map_extend [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (μ : Measure M) {s : Set M} (hsub : s ⊆ e.source)
    (f : M → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ =
      ∫⁻ y in e.extend I '' s, f ((e.extend I).symm y)
        ∂(μ.restrict e.source).map (e.extend I) := by
  have hsrc : MeasurableSet e.source := e.open_source.measurableSet
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) := .subtypeVal hsrc
  have hae : AEMeasurable (e.extend I) (μ.restrict e.source) :=
    ContinuousOn.aemeasurable
      ((e.continuousOn_extend (I := I)).mono (e.extend_source (I := I)).ge) hsrc
  have hf : ∀ z : e.source, f ((e.extend I).symm (e.source.domRestrict (e.extend I) z)) = f z :=
    fun z ↦ by
      rw [domRestrict_apply, (e.extend I).left_inv (by rw [e.extend_source]; exact z.property)]
  have hleft : ((μ.comap (Subtype.val : e.source → M)).restrict (Subtype.val ⁻¹' s)).map
      Subtype.val = μ.restrict s := by
    rw [hval.restrict_comap, hval.map_comap, Subtype.range_coe, Measure.restrict_restrict hsrc,
      Subtype.image_preimage_coe, inter_eq_right.2 hsub, inter_eq_right.2 hsub]
  rw [Measure.map_restrict_eq_map_comap_subtypeVal hsrc μ hae, hR.restrict_map, hR.lintegral_map,
    ((e.extend I).injOn.mono (e.extend_source (I := I)).ge).preimage_domRestrict_image hsub,
    ← hleft, hval.lintegral_map]
  simp only [hf]

/-- Converting a chart pushforward `withDensity` identity into a coordinate Lebesgue integral over
measurable subsets of the chart source, without measurability of the integrand. -/
theorem setLIntegral_eq_of_map_restrict_eq [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) {μ : Measure M} {ν : Measure E} {w : E → ℝ}
    (hw : ContinuousOn w (e.extend I).target)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y))
    {s : Set M} (hs : MeasurableSet s) (hsub : s ⊆ e.source) (f : M → ℝ≥0∞) :
    ∫⁻ x in s, f x ∂μ =
      ∫⁻ y in e.extend I '' s, ENNReal.ofReal (w y) * f ((e.extend I).symm y) ∂ν := by
  have hT := e.measurableSet_extend_target I
  have hA := e.measurableSet_image_extend I hs hsub
  have hAT : e.extend I '' s ⊆ (e.extend I).target := (image_mono hsub).trans
    (by rw [← e.extend_source (I := I)]; exact (e.extend I).image_source_eq_target.subset)
  have hw_ae : AEMeasurable (fun y ↦ ENNReal.ofReal (w y))
      ((ν.restrict (e.extend I).target).restrict (e.extend I '' s)) :=
    (ContinuousOn.aemeasurable (ENNReal.continuous_ofReal.comp_continuousOn hw) hT).mono_measure
      Measure.restrict_le_self
  rw [e.setLIntegral_eq_setLIntegral_map_extend I μ hsub, hmap,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ hw_ae _ hA
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
    Measure.restrict_restrict hA, inter_eq_left.2 hAT]
  simp only [Pi.mul_apply]

/-- For a measure whose pushforward along `e.extend I` has an a.e.-nonzero density `w` on
`(e.extend I).target` with respect to `ν`, an arbitrary (not necessarily measurable) subset of
`e.source` has `μ`-measure zero iff its image under `e.extend I` has `ν`-measure zero. -/
theorem measure_eq_zero_iff_image_extend_of_map_restrict_eq [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) {μ : Measure M} {ν : Measure E} {w : E → ℝ≥0∞}
    (hw : AEMeasurable w (ν.restrict (e.extend I).target))
    (hwpos : ∀ᵐ y ∂ν.restrict (e.extend I).target, w y ≠ 0)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity w)
    {s : Set M} (hsub : s ⊆ e.source) :
    μ s = 0 ↔ ν (e.extend I '' s) = 0 := by
  have himage : e.extend I '' s ⊆ (e.extend I).target :=
    (e.extend I).image_source_eq_target ▸ image_mono (by rwa [e.extend_source])
  have hν : (ν.restrict (e.extend I).target) (e.extend I '' s) = ν (e.extend I '' s) := by
    rw [Measure.restrict_apply' (e.measurableSet_extend_target I), inter_eq_left.2 himage]
  rw [← e.map_restrict_extend_apply_image I μ hsub, hmap, ← hν]
  exact ⟨fun h ↦ withDensity_absolutelyContinuous' hw hwpos h,
    fun h ↦ withDensity_absolutelyContinuous _ _ h⟩

/-- Pull a measure `ν` on the model space weighted by `g : E → ℝ≥0∞` back along the extended chart
`e.extend I` to a measure supported on `e.source`. -/
def localChartMeasure [MeasurableSpace E] [MeasurableSpace M]
    (e : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H)
    (ν : Measure E) (g : E → ℝ≥0∞) : Measure M :=
  ((ν.withDensity g).comap (e.source.domRestrict (e.extend I))).map Subtype.val

/-- `e.localChartMeasure I ν g` is supported on `e.source`. -/
@[simp]
theorem restrict_source_localChartMeasure [MeasurableSpace E]
    [MeasurableSpace M] [OpensMeasurableSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (ν : Measure E) (g : E → ℝ≥0∞) :
    (e.localChartMeasure I ν g).restrict e.source = e.localChartMeasure I ν g := by
  ext s hs
  rw [Measure.restrict_apply hs, localChartMeasure,
    Measure.map_apply measurable_subtypeVal (hs.inter e.open_source.measurableSet),
    Measure.map_apply measurable_subtypeVal hs]
  congr 1
  ext z
  simp

/-- `e.localChartMeasure I ν g` vanishes outside `e.source`. -/
@[simp]
theorem localChartMeasure_apply_compl_source [MeasurableSpace E]
    [MeasurableSpace M] [OpensMeasurableSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (ν : Measure E) (g : E → ℝ≥0∞) :
    e.localChartMeasure I ν g e.sourceᶜ = 0 := by
  rw [← e.restrict_source_localChartMeasure I ν g,
    Measure.restrict_apply e.open_source.measurableSet.compl, compl_inter_self, measure_empty]

/-- Pushing `e.localChartMeasure I ν g` forward along `e.extend I` recovers the defining weighted
restriction of `ν`. -/
theorem map_localChartMeasure_extend [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (ν : Measure E) (g : E → ℝ≥0∞) :
    (e.localChartMeasure I ν g).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity g := by
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  have hR := e.measurableEmbedding_extend_restrict I
  have hae : AEMeasurable (e.extend I) ((e.localChartMeasure I ν g).restrict e.source) :=
    ContinuousOn.aemeasurable
      ((e.continuousOn_extend (I := I)).mono (e.extend_source (I := I)).ge)
      e.open_source.measurableSet
  have hrange : Set.range (e.source.domRestrict (e.extend I)) = (e.extend I).target := by
    rw [Set.range_domRestrict, ← e.extend_source (I := I), (e.extend I).image_source_eq_target]
  rw [← e.restrict_source_localChartMeasure I ν g,
    Measure.map_restrict_eq_map_comap_subtypeVal e.open_source.measurableSet _ hae,
    localChartMeasure, hval.comap_map, hR.map_comap, hrange,
    restrict_withDensity (e.measurableSet_extend_target I)]

/-- Evaluating `e.localChartMeasure I ν g` on a measurable set pulls the integral back to
`e.extend I '' (s ∩ e.source)`. -/
theorem localChartMeasure_apply [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (ν : Measure E) (g : E → ℝ≥0∞) {s : Set M} (hs : MeasurableSet s) :
    e.localChartMeasure I ν g s =
      ∫⁻ z in e.extend I '' (s ∩ e.source), g z ∂ν := by
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  have him : e.source.domRestrict (e.extend I) '' (Subtype.val ⁻¹' s) =
      e.extend I '' (s ∩ e.source) := image_domRestrict _ _ _
  have hB : MeasurableSet (e.extend I '' (s ∩ e.source)) :=
    e.measurableSet_image_extend I (hs.inter e.open_source.measurableSet) inter_subset_right
  rw [localChartMeasure, hval.map_apply, hR.comap_apply, him, withDensity_apply _ hB]

/-- Lower integration against `e.localChartMeasure I ν g` over a measurable set reduces to a
coordinate lower integral over `e.extend I '' (s ∩ e.source)`, without measurability of `φ`. -/
theorem setLIntegral_localChartMeasure [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (ν : Measure E) {g : E → ℝ≥0∞} {s : Set M} (hs : MeasurableSet s)
    (hg : AEMeasurable g (ν.restrict (e.extend I '' (s ∩ e.source))))
    (hg_top : ∀ᵐ y ∂ν.restrict (e.extend I '' (s ∩ e.source)), g y < ∞) (φ : M → ℝ≥0∞) :
    ∫⁻ x in s, φ x ∂e.localChartMeasure I ν g =
      ∫⁻ y in e.extend I '' (s ∩ e.source), g y * φ ((e.extend I).symm y) ∂ν := by
  have hA : MeasurableSet (e.extend I '' (s ∩ e.source)) :=
    e.measurableSet_image_extend I (hs.inter e.open_source.measurableSet) inter_subset_right
  have hAT : e.extend I '' (s ∩ e.source) ⊆ (e.extend I).target :=
    (image_mono (e.extend_source (I := I) ▸ inter_subset_right)).trans
      (e.extend I).image_source_eq_target.subset
  have hR_ae : AEMeasurable g
      ((ν.restrict (e.extend I).target).restrict (e.extend I '' (s ∩ e.source))) := by
    rwa [Measure.restrict_restrict hA, inter_eq_left.2 hAT]
  have hR_top : ∀ᵐ y ∂(ν.restrict (e.extend I).target).restrict (e.extend I '' (s ∩ e.source)),
      g y < ∞ := by
    rwa [Measure.restrict_restrict hA, inter_eq_left.2 hAT]
  rw [← e.restrict_source_localChartMeasure I ν g,
    Measure.restrict_restrict hs,
    e.setLIntegral_eq_setLIntegral_map_extend I _ inter_subset_right φ,
    e.restrict_source_localChartMeasure, e.map_localChartMeasure_extend,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ hR_ae _ hA hR_top,
    Measure.restrict_restrict hA, inter_eq_left.2 hAT]
  rfl

/-- Bochner integration against `e.localChartMeasure I ν g` over a measurable set reduces to a
coordinate Bochner integral over `e.extend I '' (s ∩ e.source)`, without measurability or
integrability of `φ`. -/
theorem setIntegral_localChartMeasure [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H) (ν : Measure E) {g : E → ℝ≥0∞}
    {s : Set M} (hs : MeasurableSet s)
    (hg : AEMeasurable g (ν.restrict (e.extend I '' (s ∩ e.source))))
    (hg_top : ∀ᵐ y ∂ν.restrict (e.extend I '' (s ∩ e.source)), g y < ∞) (φ : M → F) :
    ∫ x in s, φ x ∂e.localChartMeasure I ν g =
      ∫ y in e.extend I '' (s ∩ e.source), (g y).toReal • φ ((e.extend I).symm y) ∂ν := by
  have hsrc : MeasurableSet e.source := e.open_source.measurableSet
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) := .subtypeVal hsrc
  have him : e.source.domRestrict (e.extend I) '' (Subtype.val ⁻¹' s) =
      e.extend I '' (s ∩ e.source) := image_domRestrict _ _ _
  have hA : MeasurableSet (e.extend I '' (s ∩ e.source)) :=
    e.measurableSet_image_extend I (hs.inter hsrc) inter_subset_right
  have hrange : Set.range (e.source.domRestrict (e.extend I)) = (e.extend I).target := by
    rw [Set.range_domRestrict, ← e.extend_source (I := I), (e.extend I).image_source_eq_target]
  have hArange : e.extend I '' (s ∩ e.source) ⊆ Set.range (e.source.domRestrict (e.extend I)) := by
    rw [hrange]
    exact (image_mono (e.extend_source (I := I) ▸ inter_subset_right)).trans
      (e.extend I).image_source_eq_target.subset
  have hφ (μ : Measure e.source) : ∫ z, φ z ∂μ =
      ∫ z, (fun y ↦ φ ((e.extend I).symm y)) (e.source.domRestrict (e.extend I) z) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun z ↦ by
      simp only [domRestrict_apply,
        (e.extend I).left_inv (by rw [e.extend_source]; exact z.property)])
  rw [localChartMeasure, hval.restrict_map, hval.integral_map, hR.restrict_comap, him, hφ]
  refine (hR.integral_map (fun y ↦ φ ((e.extend I).symm y))).symm.trans ?_
  rw [hR.map_comap, Measure.restrict_restrict hR.measurableSet_range, inter_eq_right.2 hArange]
  exact setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hg hg_top _ hA

end ExtendMeasure

end OpenPartialHomeomorph

end
