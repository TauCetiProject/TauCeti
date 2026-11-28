/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.Geometry.Manifold.ExtChartAt.Measurable
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Det
import TauCeti.Geometry.Manifold.ModelWithCorners.Measure

/-!
# Measure pushforwards, pullbacks, and chart change of variables for extended charts

This file provides measure-theoretic pushforward, pullback, chart-localized measure construction,
and coordinate change-of-variables lemmas for arbitrary extended charts `e.extend I` and charts of
the `C¹` maximal atlas.

## Main definitions

* `OpenPartialHomeomorph.localChartMeasure`: pull a weighted measure on the model space back along
  an extended chart `e.extend I` to a measure supported on `e.source`.

## Main results

* `OpenPartialHomeomorph.image_extend_preimage_inter`: transporting a preimage under `e₀.extend I`
  intersected with two chart sources into `e₁` equals the coordinate-change image.
* `ModelWithCorners.exists_countable_coordChange_cover`: extracting a countable subcover of
  `(e.extend I).target` by chart-overlap domains when the model space is second countable.
* `OpenPartialHomeomorph.map_restrict_extend_apply`: evaluation of `(μ.restrict e.source).map
  (e.extend I)` on a measurable set.
* `OpenPartialHomeomorph.setLIntegral_eq_setLIntegral_map_extend`: lower integrals over a subset
  of `e.source` are lower integrals in `e.extend I` against `(μ.restrict e.source).map
  (e.extend I)`, with no measurability assumption.
* `OpenPartialHomeomorph.setLIntegral_eq_of_map_restrict_eq`: converting a chart pushforward
  `withDensity` identity into a coordinate Lebesgue integral over measurable subsets of `e.source`.
* `OpenPartialHomeomorph.measure_eq_zero_iff_image_extend_of_map_restrict_eq`: a subset of
  `e.source` has `μ`-measure zero iff its extended-chart image has `ν`-measure zero when `μ` has
  a strictly positive continuous chart density.
* `OpenPartialHomeomorph.map_restrict_extend_apply_of_subset_extendCoordChange_source`:
  rewriting `((μ.restrict e.source).map (e.extend I)) A` on a subset of a chart overlap as a
  Jacobian-weighted integral of the density in the target chart.
* `OpenPartialHomeomorph.restrict_source_localChartMeasure`,
  `OpenPartialHomeomorph.localChartMeasure_apply_compl_source`,
  `OpenPartialHomeomorph.localChartMeasure_apply`, and
  `OpenPartialHomeomorph.map_restrict_localChartMeasure_apply`: support, evaluation, and
  chart-overlap pushforward formula for `OpenPartialHomeomorph.localChartMeasure`.
* `ModelWithCorners.setLIntegral_extendCoordChange`: change of variables between two charts
  of the `C¹` maximal atlas for a weighted Haar integral.
* `ModelWithCorners.eqOn_abs_det_mul_of_map_restrict_eq`: Jacobian transformation law for two
  continuous nonnegative chart weights presenting the same measure on their chart overlap.
-/

public section

open MeasureTheory Set
open scoped ENNReal Manifold Topology

noncomputable section

namespace OpenPartialHomeomorph

section ExtendMeasure

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M]

/-- Transporting the intersection of a preimage under `e₀.extend I` and two chart sources into `e₁`
agrees with the image under `I.extendCoordChange e₀ e₁` restricted to its source. -/
theorem image_extend_preimage_inter (e₀ e₁ : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (A : Set E) :
    e₁.extend I '' ((e₀.extend I ⁻¹' A ∩ e₀.source) ∩ e₁.source) =
      I.extendCoordChange e₀ e₁ '' (A ∩ (I.extendCoordChange e₀ e₁).source) := by
  ext z
  refine ⟨fun ⟨x, ⟨⟨hxA, hx0⟩, hx1⟩, hxz⟩ ↦ ?_, fun ⟨y, ⟨hyA, hyΦ⟩, hyz⟩ ↦ ?_⟩
  · refine ⟨e₀.extend I x, ⟨hxA, I.extend_mem_extendCoordChange_source hx0 hx1⟩, ?_⟩
    simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply,
      I.extendCoordChange_apply hx0] at hxz ⊢
    exact hxz
  · have hyT : y ∈ (e₀.extend I).target := hyΦ.1
    have hx1 : (e₀.extend I).symm y ∈ e₁.source := e₁.extend_source (I := I) ▸ hyΦ.2
    refine ⟨(e₀.extend I).symm y,
      ⟨⟨by rw [Set.mem_preimage, (e₀.extend I).right_inv hyT]; exact hyA,
        e₀.extend_source (I := I) ▸ (e₀.extend I).map_target hyT⟩, hx1⟩, ?_⟩
    rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply] at hyz
    exact hyz

/-- Evaluation of the pushforward of a measure restricted to a chart source along the
extended chart `e.extend I`. -/
theorem map_restrict_extend_apply [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [OpensMeasurableSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (μ : Measure M) {A : Set E} (hA : MeasurableSet A) :
    ((μ.restrict e.source).map (e.extend I)) A = μ (e.extend I ⁻¹' A ∩ e.source) := by
  rw [Measure.map_apply_of_aemeasurable
      (((e.continuousOn_extend (I := I)).mono (e.extend_source (I := I)).ge).aemeasurable
        e.open_source.measurableSet) hA,
    Measure.restrict_apply' e.open_source.measurableSet]

/-- Factor `(μ.restrict e.source).map (e.extend I)` through the subtype `e.source`. -/
private theorem map_restrict_extend_eq_map_comap [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (μ : Measure M) :
    (μ.restrict e.source).map (e.extend I) =
      (μ.comap Subtype.val).map (e.source.domRestrict (e.extend I)) := by
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  ext A hA
  rw [e.map_restrict_extend_apply I μ hA, hR.map_apply, hval.comap_apply]
  congr 1
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_image, domRestrict_apply, Subtype.exists,
    exists_and_right, exists_eq_right]
  tauto

/-- Preimage of `e.extend I '' s` under `e.source.domRestrict (e.extend I)` for `s ⊆ e.source`. -/
private theorem preimage_domRestrict_extend_image {e : OpenPartialHomeomorph M H}
    {I : ModelWithCorners 𝕜 E H} {s : Set M} (hsub : s ⊆ e.source) :
    e.source.domRestrict (e.extend I) ⁻¹' (e.extend I '' s) = Subtype.val ⁻¹' s := by
  ext z
  exact (e.extend I).injOn.mem_image_iff (by rw [e.extend_source]; exact hsub)
    (by rw [e.extend_source]; exact z.property)

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
  have hf : ∀ z : e.source, f ((e.extend I).symm (e.source.domRestrict (e.extend I) z)) = f z :=
    fun z ↦ by
      rw [domRestrict_apply, (e.extend I).left_inv (by rw [e.extend_source]; exact z.property)]
  have hleft : ((μ.comap (Subtype.val : e.source → M)).restrict (Subtype.val ⁻¹' s)).map
      Subtype.val = μ.restrict s := by
    rw [hval.restrict_comap, hval.map_comap, Subtype.range_coe, Measure.restrict_restrict hsrc,
      Subtype.image_preimage_coe, inter_eq_right.2 hsub, inter_eq_right.2 hsub]
  rw [e.map_restrict_extend_eq_map_comap I μ, hR.restrict_map, hR.lintegral_map,
    preimage_domRestrict_extend_image hsub, ← hleft, hval.lintegral_map]
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
    ((ENNReal.continuous_ofReal.comp_continuousOn hw).aemeasurable hT).mono_measure
      Measure.restrict_le_self
  rw [e.setLIntegral_eq_setLIntegral_map_extend I μ hsub, hmap,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ hw_ae _ hA
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
    Measure.restrict_restrict hA, inter_eq_left.2 hAT]
  simp only [Pi.mul_apply]

/-- For a measure whose pushforward along `e.extend I` has a strictly positive continuous density
`w` on `(e.extend I).target` with respect to `ν`, an arbitrary (not necessarily measurable) subset
of `e.source` has `μ`-measure zero iff its image under `e.extend I` has `ν`-measure zero. -/
theorem measure_eq_zero_iff_image_extend_of_map_restrict_eq [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) {μ : Measure M} {ν : Measure E} {w : E → ℝ}
    (hw : ContinuousOn w (e.extend I).target)
    (hwpos : ∀ y ∈ (e.extend I).target, 0 < w y)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y))
    {s : Set M} (hsub : s ⊆ e.source) :
    μ s = 0 ↔ ν (e.extend I '' s) = 0 := by
  have htgt : MeasurableSet (e.extend I).target := e.measurableSet_extend_target I
  have hzero : ∀ A ⊆ (e.extend I).target,
      (μ.restrict e.source).map (e.extend I) A = 0 ↔ ν A = 0 := fun A hA ↦ by
    rw [hmap, withDensity_apply_eq_zero' (f := fun y ↦ ENNReal.ofReal (w y))
      ((ENNReal.continuous_ofReal.comp_continuousOn hw).aemeasurable htgt),
      Measure.restrict_apply' htgt]
    congr! 2
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun h ↦ h.1.2, fun hy ↦ ⟨⟨(ENNReal.ofReal_pos.2 (hwpos y (hA hy))).ne', hy⟩, hA hy⟩⟩
  have himage : e.extend I '' s ⊆ (e.extend I).target :=
    (e.extend I).image_source_eq_target ▸ image_mono (by rwa [e.extend_source])
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  have hμs : (μ.restrict e.source).map (e.extend I) (e.extend I '' s) = μ s := by
    rw [e.map_restrict_extend_eq_map_comap I μ, hR.map_apply,
      preimage_domRestrict_extend_image hsub, hval.comap_apply,
      Subtype.image_preimage_coe, inter_eq_right.2 hsub]
  rw [← hμs, hzero _ himage]

/-- Pull a measure `ν` on the model space weighted by `ENNReal.ofReal ∘ f ∘ (e.extend I).symm` back
along the extended chart `e.extend I` to a measure supported on `e.source`. -/
def localChartMeasure [MeasurableSpace E] [MeasurableSpace M]
    (e : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H)
    (ν : Measure E) (f : M → ℝ) : Measure M :=
  (((ν.restrict (e.extend I).target).withDensity
      fun y ↦ ENNReal.ofReal (f ((e.extend I).symm y))).comap
    (e.source.domRestrict (e.extend I))).map Subtype.val

/-- `e.localChartMeasure I ν f` is supported on `e.source`. -/
theorem restrict_source_localChartMeasure [MeasurableSpace E]
    [MeasurableSpace M] [OpensMeasurableSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (ν : Measure E) (f : M → ℝ) :
    (e.localChartMeasure I ν f).restrict e.source = e.localChartMeasure I ν f := by
  ext s hs
  rw [Measure.restrict_apply hs, localChartMeasure,
    Measure.map_apply measurable_subtypeVal (hs.inter e.open_source.measurableSet),
    Measure.map_apply measurable_subtypeVal hs]
  congr 1
  ext z
  simp

/-- `e.localChartMeasure I ν f` vanishes outside `e.source`. -/
theorem localChartMeasure_apply_compl_source [MeasurableSpace E]
    [MeasurableSpace M] [OpensMeasurableSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (ν : Measure E) (f : M → ℝ) :
    e.localChartMeasure I ν f e.sourceᶜ = 0 := by
  rw [← e.restrict_source_localChartMeasure I ν f,
    Measure.restrict_apply e.open_source.measurableSet.compl, compl_inter_self, measure_empty]

/-- Evaluating `e.localChartMeasure I ν f` on a measurable set pulls the integral back to
`e.extend I '' (s ∩ e.source)`. -/
theorem localChartMeasure_apply [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (ν : Measure E) (f : M → ℝ) {s : Set M} (hs : MeasurableSet s) :
    e.localChartMeasure I ν f s =
      ∫⁻ z in e.extend I '' (s ∩ e.source),
        ENNReal.ofReal (f ((e.extend I).symm z)) ∂ν := by
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  have him : e.source.domRestrict (e.extend I) '' (Subtype.val ⁻¹' s) =
      e.extend I '' (s ∩ e.source) := image_domRestrict _ _ _
  have hB : MeasurableSet (e.extend I '' (s ∩ e.source)) :=
    e.measurableSet_image_extend I (hs.inter e.open_source.measurableSet) inter_subset_right
  have hBT : e.extend I '' (s ∩ e.source) ⊆ (e.extend I).target :=
    (image_mono (by simpa only [e.extend_source] using inter_subset_right)).trans
      (e.extend I).image_source_eq_target.subset
  rw [localChartMeasure, hval.map_apply, hR.comap_apply, him, withDensity_apply _ hB,
    Measure.restrict_restrict hB, inter_eq_left.2 hBT]

end ExtendMeasure

end OpenPartialHomeomorph

section

open MeasureTheory Set
open scoped ENNReal

/-- Extract a countable subcover of `(e.extend I).target` by chart-overlap domains when the model
space is second countable. -/
theorem ModelWithCorners.exists_countable_coordChange_cover
    {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SecondCountableTopology E] [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
    [TopologicalSpace M] (e : OpenPartialHomeomorph M H)
    {ι : Type*} {φ : ι → OpenPartialHomeomorph M H}
    (hcov_e : ∀ y ∈ (e.extend I).target, ∃ i, y ∈ (I.extendCoordChange e (φ i)).source) :
    ∃ t : Set ι, t.Countable ∧
      (e.extend I).target ⊆ ⋃ i ∈ t, (I.extendCoordChange e (φ i)).source := by
  have hopen (i : ι) : IsOpen (I.symm ⁻¹' (e.symm ≫ₕ φ i).source) :=
    (e.symm ≫ₕ φ i).open_source.preimage I.continuous_symm
  obtain ⟨t, ht, htcover⟩ :=
    (HereditarilyLindelofSpace.isLindelof (e.extend I).target).elim_countable_subcover
      (fun i ↦ I.symm ⁻¹' (e.symm ≫ₕ φ i).source) hopen fun y hy ↦ by
        obtain ⟨i, hyi⟩ := hcov_e y hy
        rw [I.extendCoordChange_source, I.image_eq] at hyi
        exact Set.mem_iUnion.2 ⟨i, hyi.1⟩
  refine ⟨t, ht, fun y hy ↦ ?_⟩
  obtain ⟨i, hit, hyi⟩ := Set.mem_iUnion₂.1 (htcover hy)
  refine Set.mem_iUnion₂.2 ⟨i, hit, ?_⟩
  rw [I.extendCoordChange_source, I.image_eq]
  exact ⟨hyi, e.extend_target_subset_range hy⟩

namespace ModelWithCorners

/-- Change of variables between two charts of the maximal atlas for a weighted Haar integral. -/
theorem setLIntegral_extendCoordChange {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (ν : Measure E) [ν.IsAddHaarMeasure]
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {A : Set E} (hA : MeasurableSet A) (hAsub : A ⊆ (I.extendCoordChange e e').source)
    (g : E → ℝ≥0∞) :
    ∫⁻ z in I.extendCoordChange e e' '' A, g z ∂ν =
      ∫⁻ y in A,
        ENNReal.ofReal |(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
          g (I.extendCoordChange e e' y) ∂ν := by
  have hArange : A ⊆ range I :=
    hAsub.trans (by rw [I.extendCoordChange_source]; exact image_subset_range _ _)
  have hderiv : ∀ y ∈ A,
      HasFDerivWithinAt (I.extendCoordChange e e')
        (fderivWithin ℝ (I.extendCoordChange e e') (range I) y) A y := fun y hy ↦
    ((I.contDiffWithinAt_extendCoordChange he he' (hAsub hy)).differentiableWithinAt
      one_ne_zero).hasFDerivWithinAt.mono hArange
  exact lintegral_image_eq_lintegral_abs_det_fderiv_mul ν hA hderiv
    ((I.extendCoordChange e e').injOn.mono hAsub) g

end ModelWithCorners

end

open Classical in
/-- Pushing `e₁.localChartMeasure I ν f` restricted to `e₀.source` forward along `e₀.extend I`
yields a weighted Haar integral with density `|det D(e₁ ∘ e₀⁻¹)| * f ∘ (e₀.extend I).symm`
supported on the chart overlap. -/
theorem OpenPartialHomeomorph.map_restrict_localChartMeasure_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M]
    (e₀ e₁ : OpenPartialHomeomorph M H) (I : ModelWithCorners ℝ E H)
    (he₀ : e₀ ∈ IsManifold.maximalAtlas I 1 M) (he₁ : e₁ ∈ IsManifold.maximalAtlas I 1 M)
    (ν : Measure E) [ν.IsAddHaarMeasure] (f : M → ℝ) {A : Set E} (hA : MeasurableSet A) :
    (((e₁.localChartMeasure I ν f).restrict e₀.source).map (e₀.extend I)) A =
      ∫⁻ y in A ∩ (e₀.extend I).target,
        ENNReal.ofReal
          ((I.extendCoordChange e₀ e₁).source.indicator
            (fun y ↦ |(fderivWithin ℝ (I.extendCoordChange e₀ e₁) (range I) y).det| *
              f ((e₀.extend I).symm y)) y) ∂ν := by
  set Φ := I.extendCoordChange e₀ e₁
  have hΦ_meas := I.measurableSet_extendCoordChange_source e₀ e₁
  have hT₀ : MeasurableSet (e₀.extend I).target := e₀.measurableSet_extend_target I
  have hs_meas : MeasurableSet (e₀.extend I ⁻¹' A ∩ e₀.source) :=
    e₀.measurableSet_preimage_extend_inter I hA
  rw [e₀.map_restrict_extend_apply I _ hA, e₁.localChartMeasure_apply I ν f hs_meas,
    e₀.image_extend_preimage_inter e₁ I A,
    I.setLIntegral_extendCoordChange ν he₀ he₁ (hA.inter hΦ_meas) inter_subset_right,
    ← lintegral_indicator (hA.inter hΦ_meas), ← lintegral_indicator (hA.inter hT₀)]
  refine lintegral_congr fun y ↦ ?_
  by_cases hy : y ∈ A ∩ Φ.source
  · have hyT : y ∈ A ∩ (e₀.extend I).target := ⟨hy.1, hy.2.1⟩
    rw [indicator_of_mem hy, indicator_of_mem hyT, indicator_of_mem hy.2,
      ENNReal.ofReal_mul (abs_nonneg _), I.extend_symm_extendCoordChange hy.2]
  · rw [indicator_of_notMem hy]
    by_cases hy' : y ∈ A ∩ (e₀.extend I).target
    · rw [indicator_of_mem hy', indicator_of_notMem (fun h ↦ hy ⟨hy'.1, h⟩), ENNReal.ofReal_zero]
    · rw [indicator_of_notMem hy']

/-- On a measurable subset `A ⊆ (I.extendCoordChange e e').source` of a chart overlap, the
pushforward measure `((μ.restrict e.source).map (e.extend I)) A` equals the Jacobian-weighted
Haar integral of any continuous chart weight `w'` presenting `(μ.restrict e'.source).map
(e'.extend I)` against `ν`. -/
theorem OpenPartialHomeomorph.map_restrict_extend_apply_of_subset_extendCoordChange_source
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M]
    (e e' : OpenPartialHomeomorph M H) (I : ModelWithCorners ℝ E H)
    {μ : Measure M} {ν : Measure E} [ν.IsAddHaarMeasure]
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {w' : E → ℝ} (hw' : ContinuousOn w' (e'.extend I).target)
    (hmap' : (μ.restrict e'.source).map (e'.extend I) =
      (ν.restrict (e'.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w' y))
    {A : Set E} (hA : MeasurableSet A) (hAsub : A ⊆ (I.extendCoordChange e e').source) :
    ((μ.restrict e.source).map (e.extend I)) A =
      ∫⁻ y in A,
        ENNReal.ofReal (|(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
          w' (I.extendCoordChange e e' y)) ∂ν := by
  set s := e.extend I ⁻¹' A ∩ e.source
  have hs_meas : MeasurableSet s := e.measurableSet_preimage_extend_inter I hA
  have hse' : s ⊆ e'.source := fun x ⟨hxA, _⟩ ↦ by
    have h2 : (e.extend I).symm (e.extend I x) ∈ (e'.extend I).source := (hAsub hxA).2
    rwa [(e.extend I).left_inv (by rwa [e.extend_source]), e'.extend_source] at h2
  have him : e'.extend I '' s = I.extendCoordChange e e' '' A := by
    rw [← inter_eq_left.2 hse', e.image_extend_preimage_inter e' I A, inter_eq_left.2 hAsub]
  have h := e'.setLIntegral_eq_of_map_restrict_eq I hw' hmap' hs_meas hse' (fun _ ↦ 1)
  simp only [mul_one, setLIntegral_one] at h
  rw [e.map_restrict_extend_apply I μ hA, h, him,
    I.setLIntegral_extendCoordChange ν he he' hA hAsub]
  exact setLIntegral_congr_fun hA fun y _ ↦ (ENNReal.ofReal_mul (abs_nonneg _)).symm

namespace ModelWithCorners

section OverlapJacobian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M] [BorelSpace M]

/-- Shared Jacobian transformation identity for two continuous nonnegative chart weights presenting
the same measure on their chart overlap. -/
theorem eqOn_abs_det_mul_of_map_restrict_eq
    {μ : Measure M} {ν : Measure E} [ν.IsAddHaarMeasure]
    {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {w w' : E → ℝ}
    (hw : ContinuousOn w (e.extend I).target) (hw' : ContinuousOn w' (e'.extend I).target)
    (hw0 : ∀ y ∈ (e.extend I).target, 0 ≤ w y) (hw'0 : ∀ y ∈ (e'.extend I).target, 0 ≤ w' y)
    (hmap : (μ.restrict e.source).map (e.extend I) =
      (ν.restrict (e.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w y))
    (hmap' : (μ.restrict e'.source).map (e'.extend I) =
      (ν.restrict (e'.extend I).target).withDensity fun y ↦ ENNReal.ofReal (w' y)) :
    EqOn w (fun y ↦ |(fderivWithin ℝ (I.extendCoordChange e e') (range I) y).det| *
      w' (I.extendCoordChange e e' y)) (I.extendCoordChange e e').source := by
  set Φ := I.extendCoordChange e e'
  have hΦ_src : Φ.source = I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I := by
    rw [I.extendCoordChange_source, I.image_eq]
  have hΦ_meas : MeasurableSet Φ.source := I.measurableSet_extendCoordChange_source e e'
  have hsubT : Φ.source ⊆ (e.extend I).target := fun _ hy ↦ hy.1
  have hmeq :
      (ν.restrict Φ.source).withDensity (fun y ↦ ENNReal.ofReal (w y)) =
        (ν.restrict Φ.source).withDensity fun y ↦
          ENNReal.ofReal (|(fderivWithin ℝ Φ (range I) y).det| * w' (Φ y)) := by
    ext A hA
    have h1 := withDensity_apply (fun y ↦ ENNReal.ofReal (w y)) (hA.inter hΦ_meas)
      (μ := ν.restrict (e.extend I).target)
    rw [Measure.restrict_restrict (hA.inter hΦ_meas),
      inter_eq_left.2 (inter_subset_right.trans hsubT), ← hmap,
      e.map_restrict_extend_apply_of_subset_extendCoordChange_source e' I he he' hw' hmap'
        (hA.inter hΦ_meas) inter_subset_right] at h1
    rw [withDensity_apply _ hA, withDensity_apply _ hA, Measure.restrict_restrict hA, h1]
  have hcont_rhs : ContinuousOn
      (fun y ↦ |(fderivWithin ℝ Φ (range I) y).det| * w' (Φ y)) Φ.source :=
    (I.continuousOn_abs_det_fderivWithin_extendCoordChange he he').mul
      (hw'.comp (I.contDiffOn_extendCoordChange he he').continuousOn fun _ hy ↦
        (Φ.map_source hy).1)
  rw [hΦ_src] at hmeq hcont_rhs ⊢
  exact I.eqOn_of_withDensity_ofReal_eq (e.symm ≫ₕ e').open_source
    (hw.mono (hΦ_src ▸ hsubT)) hcont_rhs
    (fun y hy ↦ hw0 y (hsubT (hΦ_src.symm ▸ hy)))
    (fun y hy ↦ mul_nonneg (abs_nonneg _) (hw'0 _ (Φ.map_source (hΦ_src.symm ▸ hy)).1)) hmeq

end OverlapJacobian

end ModelWithCorners

end
