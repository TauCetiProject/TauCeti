/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Measurability and Jacobian determinants of extended charts

This file provides measurability, measurable-embedding, coordinate-change source measurability,
and chart-pushforward evaluation lemmas for arbitrary extended charts `e.extend I`, together with
continuity, positivity, the chain rule for the absolute Jacobian determinant of `C¹` extended
coordinate changes, and the chart change-of-variables formula for Lebesgue integrals.

## Main results

* `OpenPartialHomeomorph.measurableSet_extend_target`,
  `OpenPartialHomeomorph.measurableEmbedding_extend_restrict`,
  `OpenPartialHomeomorph.measurableSet_image_extend`,
  `OpenPartialHomeomorph.measurableSet_preimage_extend_inter`,
  `OpenPartialHomeomorph.measurableSet_extendCoordChange_source`,
  `OpenPartialHomeomorph.map_restrict_extend_apply`: measurability and measure-pushforward lemmas
  for arbitrary extended charts `e.extend I`.
* `TauCeti.continuousOn_abs_det_fderivWithin_extendCoordChange`,
  `TauCeti.abs_det_fderivWithin_extendCoordChange_pos`,
  `TauCeti.abs_det_fderivWithin_extendCoordChange_comp`: continuity, positivity, and chain rule
  for the absolute Jacobian determinant of `C¹` extended coordinate changes.
* `MeasureTheory.Measure.setLIntegral_extendCoordChange`: change of variables between two charts
  of the `C¹` maximal atlas for a weighted Haar integral.
-/

public section

open scoped Manifold Topology

namespace OpenPartialHomeomorph

section ExtendMeasurability

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M]

/-- The target of an extended chart `e.extend I` is measurable in any measurable space on `E`
where open sets are measurable. -/
theorem measurableSet_extend_target [MeasurableSpace E] [OpensMeasurableSpace E]
    (e : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H) :
    MeasurableSet (e.extend I).target := by
  rw [e.extend_target]
  exact (e.open_target.preimage I.continuous_symm).measurableSet.inter
    I.isClosed_range.measurableSet

/-- An extended chart `e.extend I`, restricted to its source, is a measurable embedding for the
Borel measurable spaces. -/
theorem measurableEmbedding_extend_restrict [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) :
    MeasurableEmbedding (e.source.domRestrict (e.extend I)) := by
  let f : PartialHomeomorph M E :=
    { toPartialEquiv := e.extend I
      continuousOn_toFun := e.continuousOn_extend
      continuousOn_invFun := e.continuousOn_extend_symm }
  have hrange : MeasurableSet (Set.range (f.source.domRestrict f)) := by
    rw [Set.range_domRestrict, f.image_source_eq_target]
    exact e.measurableSet_extend_target I
  have hemb := f.isEmbedding_restrict.measurableEmbedding hrange
  rwa [e.extend_source] at hemb

/-- For a Borel measurable space on `M`, the image under `e.extend I` of a measurable subset of
`e.source` is measurable in any measurable space on `E` where open sets are measurable. -/
theorem measurableSet_image_extend [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) {s : Set M} (hs : MeasurableSet s) (hsub : s ⊆ e.source) :
    MeasurableSet (e.extend I '' s) :=
  OpensMeasurableSpace.borel_le _ <| by
    let : MeasurableSpace E := borel E
    have : BorelSpace E := ⟨rfl⟩
    have him : e.source.domRestrict (e.extend I) '' (Subtype.val ⁻¹' s) = e.extend I '' s := by
      rw [Set.image_domRestrict, Set.inter_eq_left.2 hsub]
    rw [← him]
    exact (e.measurableEmbedding_extend_restrict I).measurableSet_image.2
      (hs.preimage measurable_subtypeVal)

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

/-- Evaluation of the pushforward of a measure restricted to a chart source along the
extended chart `e.extend I`. -/
theorem map_restrict_extend_apply [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [OpensMeasurableSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) (μ : MeasureTheory.Measure M) {A : Set E} (hA : MeasurableSet A) :
    ((μ.restrict e.source).map (e.extend I)) A = μ (e.extend I ⁻¹' A ∩ e.source) := by
  have hcont : Continuous (e.source.domRestrict (e.extend I)) := by
    rw [← continuousOn_iff_continuous_domRestrict, ← e.extend_source (I := I)]
    exact e.continuousOn_extend
  rw [MeasureTheory.Measure.map_apply_of_aemeasurable
      (aemeasurable_restrict_of_measurable_subtype e.open_source.measurableSet
        hcont.measurable) hA,
    MeasureTheory.Measure.restrict_apply' e.open_source.measurableSet]

end ExtendMeasurability

end OpenPartialHomeomorph

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
