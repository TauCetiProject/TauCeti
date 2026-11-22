/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.MeasureTheory.Function.Jacobian
import TauCeti.MeasureTheory.Measure.Subtype
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Measure pushforwards and Jacobian determinants of extended charts

This file provides measure-theoretic pushforward, pullback, and coordinate integration lemmas for
arbitrary extended charts `e.extend I`, full-support and density-uniqueness lemmas for additive Haar
measures restricted to relatively open subsets of `Set.range I`, together with continuity,
positivity, the chain rule for the absolute Jacobian determinant of `C¹` extended coordinate
changes, and the chart change-of-variables formula for Lebesgue integrals.

## Main results

* `OpenPartialHomeomorph.measurableSet_preimage_extend_inter`,
  `OpenPartialHomeomorph.measurableSet_extendCoordChange_source`,
  `OpenPartialHomeomorph.image_extend_preimage_inter`,
  `OpenPartialHomeomorph.exists_countable_coordChange_cover`: measurability, coordinate-overlap
  image-preimage identity, and countable overlap covers for extended charts.
* `OpenPartialHomeomorph.map_restrict_extend_apply`: evaluation of `(μ.restrict e.source).map
  (e.extend I)` on a measurable set.
* `OpenPartialHomeomorph.comap_restrict_eq_comap_map_restrict`: pulling `μ.restrict e.source` back
  to `e.source` agrees with pulling `(μ.restrict e.source).map (e.extend I)` back along
  `e.source.domRestrict (e.extend I)`.
* `OpenPartialHomeomorph.setLIntegral_eq_of_map_restrict_eq`: converting a chart pushforward
  `withDensity` identity into a coordinate Lebesgue integral over measurable subsets of `e.source`.
* `ModelWithCorners.isOpenPosMeasure_comap_range_inter`: pulling an additive Haar measure back to
  a relatively open subset of `Set.range I` yields an open-positive measure.
* `ModelWithCorners.eqOn_of_withDensity_ofReal_eq`: continuous nonnegative real densities presenting
  the same weighted Haar measure on a relatively open subset of `Set.range I` agree pointwise there.
* `TauCeti.continuousOn_abs_det_fderivWithin_extendCoordChange`,
  `TauCeti.abs_det_fderivWithin_extendCoordChange_pos`,
  `TauCeti.abs_det_fderivWithin_extendCoordChange_comp`: continuity, positivity, and chain rule
  for the absolute Jacobian determinant of `C¹` extended coordinate changes.
* `MeasureTheory.Measure.setLIntegral_extendCoordChange`: change of variables between two charts
  of the `C¹` maximal atlas for a weighted Haar integral.
-/

public section

open MeasureTheory Set
open scoped ENNReal Manifold Topology

namespace OpenPartialHomeomorph

section ExtendMeasure

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M]

/-- The preimage of a Borel measurable set in `E` under `e.extend I`, intersected with `e.source`,
is measurable whenever open subsets of `M` are measurable. -/
theorem measurableSet_preimage_extend_inter [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [OpensMeasurableSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) {A : Set E} (hA : MeasurableSet A) :
    MeasurableSet (e.extend I ⁻¹' A ∩ e.source) := by
  have hcont : Continuous (e.source.domRestrict (e.extend I)) := by
    rw [← continuousOn_iff_continuous_domRestrict, ← e.extend_source (I := I)]
    exact e.continuousOn_extend
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  have hseq : e.extend I ⁻¹' A ∩ e.source =
      Subtype.val '' (e.source.domRestrict (e.extend I) ⁻¹' A) := by
    ext x
    simp [and_comm]
  rw [hseq]
  exact hval.measurableSet_image.2 (hcont.measurable hA)

/-- The source of an extended coordinate change is measurable whenever open subsets of `E`
are measurable. -/
theorem measurableSet_extendCoordChange_source [MeasurableSpace E] [OpensMeasurableSpace E]
    (e e' : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H) :
    MeasurableSet (I.extendCoordChange e e').source := by
  rw [I.extendCoordChange_source, I.image_eq]
  exact ((e.symm ≫ₕ e').open_source.preimage I.continuous_symm).measurableSet.inter
    I.isClosed_range.measurableSet

/-- Transporting the intersection of a preimage under `e₀.extend I` and two chart sources into `e₁`
agrees with the image under `I.extendCoordChange e₀ e₁` restricted to its source. -/
theorem image_extend_preimage_inter (e₀ e₁ : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (A : Set E) :
    e₁.extend I '' ((e₀.extend I ⁻¹' A ∩ e₀.source) ∩ e₁.source) =
      I.extendCoordChange e₀ e₁ '' (A ∩ (I.extendCoordChange e₀ e₁).source) := by
  ext z
  refine ⟨fun ⟨x, ⟨⟨hxA, hx0⟩, hx1⟩, hxz⟩ ↦ ?_, fun ⟨y, ⟨hyA, hyΦ⟩, hyz⟩ ↦ ?_⟩
  · refine ⟨e₀.extend I x, ⟨hxA, ?_⟩, ?_⟩
    · rw [← OpenPartialHomeomorph.extend_image_source_inter (f := e₀) (f' := e₁)]
      exact Set.mem_image_of_mem _ ⟨hx0, hx1⟩
    · have hx0' : x ∈ (e₀.extend I).source := by rwa [e₀.extend_source]
      rw [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
        (e₀.extend I).left_inv hx0']
      exact hxz
  · have hyT : y ∈ (e₀.extend I).target := hyΦ.1
    have hx1 : (e₀.extend I).symm y ∈ e₁.source := e₁.extend_source (I := I) ▸ hyΦ.2
    refine ⟨(e₀.extend I).symm y,
      ⟨⟨by rw [Set.mem_preimage, (e₀.extend I).right_inv hyT]; exact hyA, ?_⟩, hx1⟩, hyz⟩
    simpa only [← e₀.extend_source (I := I)] using (e₀.extend I).map_target hyT

/-- Extract a countable subcover of `(e.extend I).target` by chart-overlap domains when the model
space is second countable. -/
theorem exists_countable_coordChange_cover [SecondCountableTopology E]
    (e : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H)
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

/-- Evaluation of the pushforward of a measure restricted to a chart source along the
extended chart `e.extend I`. -/
theorem map_restrict_extend_apply [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [OpensMeasurableSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (μ : Measure M) {A : Set E} (hA : MeasurableSet A) :
    ((μ.restrict e.source).map (e.extend I)) A = μ (e.extend I ⁻¹' A ∩ e.source) := by
  have hcont : Continuous (e.source.domRestrict (e.extend I)) := by
    rw [← continuousOn_iff_continuous_domRestrict, ← e.extend_source (I := I)]
    exact e.continuousOn_extend
  rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_restrict_of_measurable_subtype e.open_source.measurableSet
        hcont.measurable) hA,
    Measure.restrict_apply' e.open_source.measurableSet]

/-- Pulling `μ.restrict e.source` back to `e.source` agrees with pulling the chart pushforward
`(μ.restrict e.source).map (e.extend I)` back along `e.source.domRestrict (e.extend I)`. -/
theorem comap_restrict_eq_comap_map_restrict [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (μ : Measure M) :
    (μ.restrict e.source).comap (Subtype.val : e.source → M) =
      ((μ.restrict e.source).map (e.extend I)).comap (e.source.domRestrict (e.extend I)) := by
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  ext B hB
  have hBs : MeasurableSet (Subtype.val '' B : Set M) := hval.measurableSet_image' hB
  have hBim : MeasurableSet (e.source.domRestrict (e.extend I) '' B) := hR.measurableSet_image' hB
  rw [hval.comap_apply, hR.comap_apply, e.map_restrict_extend_apply I μ hBim,
    Measure.restrict_apply hBs, inter_eq_left.2 (Subtype.coe_image_subset e.source B)]
  congr 1
  ext x
  refine ⟨fun ⟨z, hzB, hzx⟩ ↦ ?_, fun ⟨⟨z, hzB, hzx⟩, hxe⟩ ↦ ?_⟩
  · subst hzx
    exact ⟨⟨z, hzB, rfl⟩, z.property⟩
  · have hzs : z.val ∈ (e.extend I).source := by simpa only [e.extend_source] using z.property
    have hxs : x ∈ (e.extend I).source := by rwa [e.extend_source]
    exact ⟨z, hzB, (e.extend I).injOn hzs hxs hzx⟩

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
  have hR := e.measurableEmbedding_extend_restrict I
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  have hT := e.measurableSet_extend_target I
  have hA := e.measurableSet_image_extend I hs hsub
  have hAT : e.extend I '' s ⊆ (e.extend I).target := (image_mono hsub).trans
    (by rw [← e.extend_source (I := I)]; exact (e.extend I).image_source_eq_target.subset)
  have hrestrict : μ.restrict s =
      ((((ν.restrict (e.extend I).target).withDensity (fun y ↦ ENNReal.ofReal (w y))).comap
        (e.source.domRestrict (e.extend I))).restrict (Subtype.val ⁻¹' s)).map Subtype.val := by
    rw [← hmap, ← e.comap_restrict_eq_comap_map_restrict I μ, ← hval.restrict_map, hval.map_comap,
      Subtype.range_coe, Measure.restrict_restrict e.open_source.measurableSet, inter_self,
      Measure.restrict_restrict hs, inter_eq_left.2 hsub]
  have him : e.source.domRestrict (e.extend I) '' (Subtype.val ⁻¹' s) = e.extend I '' s := by
    rw [image_domRestrict, inter_eq_left.2 hsub]
  have hcongr (ρ : Measure e.source) :
      ∫⁻ z, f z ∂ρ =
        ∫⁻ z, (fun y ↦ f ((e.extend I).symm y)) (e.source.domRestrict (e.extend I) z) ∂ρ :=
    lintegral_congr fun z ↦ by
      have hz : z.val ∈ (e.extend I).source := by simpa only [e.extend_source] using z.property
      simp only [domRestrict_apply, (e.extend I).left_inv hz]
  rw [hrestrict, hval.lintegral_map, hR.restrict_comap, him, hcongr]
  refine (hR.lintegral_map (fun y ↦ f ((e.extend I).symm y))).symm.trans ?_
  have hw_ae : AEMeasurable (fun y ↦ ENNReal.ofReal (w y))
      ((ν.restrict (e.extend I).target).restrict (e.extend I '' s)) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn hw).aemeasurable hT).mono_measure
      Measure.restrict_le_self
  rw [hR.map_comap, Measure.restrict_restrict hR.measurableSet_range,
    inter_eq_right.2 (him ▸ image_subset_range _ _),
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀ _ hw_ae _ hA
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top),
    Measure.restrict_restrict hA, inter_eq_left.2 hAT]
  rfl

end ExtendMeasure

end OpenPartialHomeomorph

namespace ModelWithCorners

section HaarDensity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- Pulling an additive Haar measure back to a relatively open subset of `range I` yields a
measure positive on nonempty relatively open subsets. -/
theorem isOpenPosMeasure_comap_range_inter (I : ModelWithCorners ℝ E H)
    [MeasurableSpace E] [BorelSpace E] (ν : Measure E) [ν.IsAddHaarMeasure]
    {U : Set H} (hU : IsOpen U) :
    (ν.comap (Subtype.val : (I.symm ⁻¹' U ∩ range I : Set E) → E)).IsOpenPosMeasure := by
  set V : Set E := I.symm ⁻¹' U ∩ range I
  have hV : MeasurableSet V :=
    (hU.preimage I.continuous_symm).measurableSet.inter I.isClosed_range.measurableSet
  refine ⟨fun W hW ⟨⟨y, hyV⟩, hyW⟩ ↦ ?_⟩
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.1 hW
  have hyO : y ∈ O := by simpa [← hOW] using hyW
  have hO' : IsOpen (O ∩ I.symm ⁻¹' U) := hO.inter (hU.preimage I.continuous_symm)
  obtain ⟨z, hz⟩ := mem_closure_iff_nhds.1 (I.range_subset_closure_interior hyV.2)
    (O ∩ I.symm ⁻¹' U) (hO'.mem_nhds ⟨hyO, hyV.1⟩)
  have hopen : IsOpen ((O ∩ I.symm ⁻¹' U) ∩ interior (range I)) := hO'.inter isOpen_interior
  have hsub : (O ∩ I.symm ⁻¹' U) ∩ interior (range I) ⊆ Subtype.val '' W := by
    rintro w ⟨⟨hwO, hwU⟩, hwI⟩
    exact ⟨⟨w, ⟨hwU, interior_subset hwI⟩⟩, by simpa [← hOW] using hwO, rfl⟩
  rw [(MeasurableEmbedding.subtypeVal hV).comap_apply]
  exact ((hopen.measure_pos ν ⟨z, hz⟩).trans_le (measure_mono hsub)).ne'

/-- Continuous nonnegative real densities presenting the same weighted Haar measure on a
relatively open subset of `range I` agree pointwise there. -/
theorem eqOn_of_withDensity_ofReal_eq (I : ModelWithCorners ℝ E H) [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [ν.IsAddHaarMeasure]
    {U : Set H} (hU : IsOpen U) {w₁ w₂ : E → ℝ}
    (hw₁ : ContinuousOn w₁ (I.symm ⁻¹' U ∩ range I))
    (hw₂ : ContinuousOn w₂ (I.symm ⁻¹' U ∩ range I))
    (h1 : ∀ y ∈ I.symm ⁻¹' U ∩ range I, 0 ≤ w₁ y)
    (h2 : ∀ y ∈ I.symm ⁻¹' U ∩ range I, 0 ≤ w₂ y)
    (heq : (ν.restrict (I.symm ⁻¹' U ∩ range I)).withDensity (fun y ↦ ENNReal.ofReal (w₁ y)) =
      (ν.restrict (I.symm ⁻¹' U ∩ range I)).withDensity (fun y ↦ ENNReal.ofReal (w₂ y))) :
    EqOn w₁ w₂ (I.symm ⁻¹' U ∩ range I) := by
  set V : Set E := I.symm ⁻¹' U ∩ range I
  have hV : MeasurableSet V :=
    (hU.preimage I.continuous_symm).measurableSet.inter I.isClosed_range.measurableSet
  have hval : MeasurableEmbedding (Subtype.val : V → E) := .subtypeVal hV
  have : (ν.comap (Subtype.val : V → E)).IsOpenPosMeasure :=
    I.isOpenPosMeasure_comap_range_inter ν hU
  have hcomap (w : E → ℝ) :
      ((ν.restrict V).withDensity (fun y ↦ ENNReal.ofReal (w y))).comap (Subtype.val : V → E) =
        (ν.comap (Subtype.val : V → E)).withDensity fun y ↦ ENNReal.ofReal (w y.val) := by
    ext A hA
    rw [hval.comap_apply, withDensity_apply _ (hval.measurableSet_image' hA),
      withDensity_apply _ hA, Measure.restrict_restrict (hval.measurableSet_image' hA),
      inter_eq_left.2 (Subtype.coe_image_subset V A),
      hval.restrict_comap, ← hval.lintegral_map (fun y ↦ ENNReal.ofReal (w y)), hval.map_comap,
      Subtype.range_coe, Measure.restrict_restrict hV,
      inter_eq_right.2 (Subtype.coe_image_subset V A)]
  have hsubEq :
      (ν.comap (Subtype.val : V → E)).withDensity (fun y ↦ ENNReal.ofReal (w₁ y.val)) =
        (ν.comap (Subtype.val : V → E)).withDensity fun y ↦ ENNReal.ofReal (w₂ y.val) := by
    rw [← hcomap w₁, ← hcomap w₂, heq]
  have hfun := MeasureTheory.continuous_eq_of_withDensity_ofReal_eq
    (continuousOn_iff_continuous_domRestrict.1 hw₁)
    (continuousOn_iff_continuous_domRestrict.1 hw₂)
    (fun y ↦ h1 y.val y.property) (fun y ↦ h2 y.val y.property) hsubEq
  exact fun y hy ↦ congrFun hfun ⟨y, hy⟩

end HaarDensity

end ModelWithCorners

namespace TauCeti

section ExtendCoordChangeDet

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M]

private theorem fderivWithin_extendCoordChange_eq_source
    {e e' : OpenPartialHomeomorph M H} {y : E} (hy : y ∈ (I.extendCoordChange e e').source) :
    fderivWithin ℝ (I.extendCoordChange e e') (Set.range I) y =
      fderivWithin ℝ (I.extendCoordChange e e') (I.extendCoordChange e e').source y := by
  refine fderivWithin_congr_set ?_
  have hsub : (I.extendCoordChange e e').source ⊆ Set.range I := by
    rw [I.extendCoordChange_source]
    exact Set.image_subset_range _ _
  have h := nhdsWithin_restrict'' (Set.range I) (I.extendCoordChange_source_mem_nhdsWithin hy)
  rw [Set.inter_eq_right.2 hsub] at h
  exact nhdsWithin_eq_iff_eventuallyEqSet.1 h

/-- The absolute Jacobian determinant of a `C¹` extended coordinate change is continuous on
its source. -/
theorem continuousOn_abs_det_fderivWithin_extendCoordChange
    [ChartedSpace H M] {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M) :
    ContinuousOn
      (fun y ↦ |(fderivWithin ℝ (I.extendCoordChange e e') (Set.range I) y).det|)
      (I.extendCoordChange e e').source := by
  set Φ := I.extendCoordChange e e'
  have hcont : ContinuousOn (fun y ↦ fderivWithin ℝ Φ Φ.source y) Φ.source :=
    (I.contDiffOn_extendCoordChange he he').continuousOn_fderivWithin
      I.uniqueDiffOn_extendCoordChange_source le_rfl
  have hdet : ContinuousOn (fun y ↦ |(fderivWithin ℝ Φ Φ.source y).det|) Φ.source :=
    (continuous_abs.comp ContinuousLinearMap.continuous_det).comp_continuousOn hcont
  exact hdet.congr fun y hy ↦ by rw [fderivWithin_extendCoordChange_eq_source hy]

/-- The absolute Jacobian determinant of a `C¹` extended coordinate change is strictly
positive at every point of its source. -/
theorem abs_det_fderivWithin_extendCoordChange_pos
    [ChartedSpace H M] {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    {y : E} (hy : y ∈ (I.extendCoordChange e e').source) :
    0 < |(fderivWithin ℝ (I.extendCoordChange e e') (Set.range I) y).det| := by
  rw [fderivWithin_extendCoordChange_eq_source hy, abs_pos]
  obtain ⟨A, hA⟩ := I.isInvertible_fderivWithin_extendCoordChange one_ne_zero he he' hy
  rw [← hA]
  exact A.toLinearEquiv.isUnit_det'.ne_zero

/-- Chain rule for the absolute Jacobian determinants of `C¹` extended coordinate changes on a
triple chart overlap. -/
theorem abs_det_fderivWithin_extendCoordChange_comp
    [ChartedSpace H M] {e e' e'' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    (he'' : e'' ∈ IsManifold.maximalAtlas I 1 M) {x : M}
    (hxe : x ∈ e.source) (hxe' : x ∈ e'.source) (hxe'' : x ∈ e''.source) :
    |(fderivWithin ℝ (I.extendCoordChange e e'') (Set.range I) (e.extend I x)).det| =
      |(fderivWithin ℝ (I.extendCoordChange e' e'') (Set.range I) (e'.extend I x)).det| *
        |(fderivWithin ℝ (I.extendCoordChange e e') (Set.range I) (e.extend I x)).det| := by
  set y := e.extend I x
  set z := e'.extend I x
  have hy_ee' : y ∈ (I.extendCoordChange e e').source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter (f := e) (f' := e')]
    exact Set.mem_image_of_mem _ ⟨hxe, hxe'⟩
  have hz_e'e'' : z ∈ (I.extendCoordChange e' e'').source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter (f := e') (f' := e'')]
    exact Set.mem_image_of_mem _ ⟨hxe', hxe''⟩
  have hΦy : I.extendCoordChange e e' y = z := by
    have hye : x ∈ (e.extend I).source := by rwa [e.extend_source]
    simp only [y, z, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
      (e.extend I).left_inv hye]
  have hd1 : DifferentiableWithinAt ℝ (I.extendCoordChange e e') (Set.range I) y :=
    (I.contDiffWithinAt_extendCoordChange he he' hy_ee').differentiableWithinAt one_ne_zero
  have hd2 : DifferentiableWithinAt ℝ (I.extendCoordChange e' e'') (Set.range I) z :=
    (I.contDiffWithinAt_extendCoordChange he' he'' hz_e'e'').differentiableWithinAt one_ne_zero
  have hU : UniqueDiffWithinAt ℝ (Set.range I) y :=
    I.uniqueDiffOn y (e.extend_target_subset_range
      ((e.extend I).map_source (by rwa [e.extend_source])))
  have hmaps : Set.MapsTo (I.extendCoordChange e e') (Set.range I) (Set.range I) := fun _ _ ↦
    Set.mem_range_self _
  have heq : I.extendCoordChange e e'' =ᶠ[𝓝[Set.range I] y]
      I.extendCoordChange e' e'' ∘ I.extendCoordChange e e' := by
    have hmem : (I.extendCoordChange e e').source ∩ (I.extendCoordChange e e'').source ∈
        𝓝[Set.range I] y :=
      Filter.inter_mem (I.extendCoordChange_source_mem_nhdsWithin' hxe hxe')
        (I.extendCoordChange_source_mem_nhdsWithin' hxe hxe'')
    filter_upwards [hmem] with w hw
    have hxw' : (e.extend I).symm w ∈ (e'.extend I).source := hw.1.2
    simp only [Function.comp_apply, ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply,
      (e'.extend I).left_inv hxw']
  have heq0 : I.extendCoordChange e e'' y =
      (I.extendCoordChange e' e'' ∘ I.extendCoordChange e e') y := by
    have hxw' : x ∈ (e'.extend I).source := by rwa [e'.extend_source]
    have hxe_s : x ∈ (e.extend I).source := by rwa [e.extend_source]
    simp only [Function.comp_apply, y, ModelWithCorners.extendCoordChange,
      PartialEquiv.trans_apply, (e.extend I).left_inv hxe_s, (e'.extend I).left_inv hxw']
  rw [heq.fderivWithin_eq heq0, fderivWithin_comp y (hΦy ▸ hd2) hd1 hmaps hU, hΦy]
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    abs_mul]

end ExtendCoordChangeDet

end TauCeti

section

open MeasureTheory Set
open scoped ENNReal

namespace MeasureTheory.Measure

/-- Change of variables between two charts of the maximal atlas for a weighted Haar integral. -/
theorem setLIntegral_extendCoordChange {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
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

end MeasureTheory.Measure

end
