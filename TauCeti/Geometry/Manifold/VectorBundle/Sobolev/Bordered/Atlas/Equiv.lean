/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Independence of the Sobolev space of sections over a surface with boundary from the atlas

Let `M` be a `C¹` manifold modelled on the closed upper half-plane `ClosedUpperHalfPlane`, for
instance a surface with boundary, let `V → M` be a real vector bundle with finite-dimensional
model fibre `F`, and let `A`, `A'` be two finite bundle atlases. The Sobolev spaces `W^{k,p}(V)` of
`TauCeti.BorderedSobolevSection A p k` and `TauCeti.BorderedSobolevSection A' p k` consist of
tuples of chartwise components of sections, on the interiors in `ℂ` of the images of the charts of
`A` and of `A'`. This file shows that, whenever every section with `W^{k,p}` components in the
charts of `A` also has `W^{k,p}` components in the charts of `A'`
(`TauCeti.BorderedSobolevSection.TransfersTo A A' p k`), sending an element to the element of the
other atlas with the same section is a continuous linear map
(`TauCeti.BorderedSobolevSection.changeAtlas`). When the property holds in both directions the
two spaces are isomorphic Banach spaces (`TauCeti.BorderedSobolevSection.atlasEquiv`), so their
norms are equivalent (`TauCeti.BorderedSobolevSection.exists_norm_changeAtlas_le`).

This is the analogue for bases with boundary of
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Atlas.Equiv`, and the argument is the same. The
map is well defined because chart transitions between the two atlases carry null sets to null
sets. A chart transition is defined on a relatively open subset of the closed upper half-plane; it
carries points of positive imaginary part to points of positive imaginary part
(`TauCeti.ClosedUpperHalfPlane.im_pos_iff_of_mem_contDiffGroupoid`), and its inverse is
differentiable there, so it preserves Lebesgue null sets in the interiors of the chart images
(`TauCeti.FiniteBundleAtlas.ae_restrict_halfImage_chart_symm`). Hence two sections whose readings
agree almost everywhere in the charts of `A` agree almost everywhere in the charts of `A'`
(`TauCeti.FiniteBundleAtlas.halfCoord_ae_eq_of_halfCoord_ae_eq`). Continuity follows from the
closed graph theorem: along a subsequence the chart data converge almost everywhere, and on the
overlap of a chart of `A` and a chart of `A'` the readings are related by the coordinate changes of
the bundle, which are continuous linear maps.

## Main definitions

* `TauCeti.BorderedSobolevSection.TransfersTo A A' p k`: every section with `W^{k,p}` components
  in the charts of `A` has `W^{k,p}` components in the charts of `A'`.
* `TauCeti.BorderedSobolevSection.changeAtlas`: the continuous linear map between the Sobolev
  spaces of two atlases sending an element to the element with the same section.
* `TauCeti.BorderedSobolevSection.atlasEquiv`: the isomorphism of Banach spaces between them.

## Main results

* `TauCeti.FiniteBundleAtlas.ae_restrict_halfImage_symm_of_ae`: almost everywhere statements on
  `M` do not depend on the atlas.
* `TauCeti.FiniteBundleAtlas.halfCoord_ae_eq_of_halfCoord_ae_eq`: sections whose readings agree
  almost everywhere in one atlas agree almost everywhere in every other atlas.
* `TauCeti.BorderedSobolevSection.chartValueL_changeAtlas_ae`: the chart data of
  `changeAtlas h w` are the readings in `A'` of any section of `w`.
* `TauCeti.BorderedSobolevSection.exists_norm_changeAtlas_le`: when sections transfer in both
  directions the norms of the two atlases are equivalent.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Appendix C.1.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Set TopologicalSpace
open scoped Manifold Topology ENNReal

namespace TauCeti

section Measure

/-! ### Null sets and changes of atlas -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  [IsManifold closedUpperHalfPlaneModel 1 M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  {F' : Type*} [TopologicalSpace F'] {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, TopologicalSpace (V' x)] [FiberBundle F' V']

namespace FiniteBundleAtlas

variable (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

/-- A point of `M` lying in the domain of chart `i` of `A`, and read in chart `i'` of `A'` at a
point of the interior of the image of that chart, is read in chart `i` at a point of the interior
of the image of chart `i`: chart transitions preserve the sign of the imaginary part. -/
theorem coe_chart_mem_halfImage (A' : FiniteBundleAtlas ClosedUpperHalfPlane M F' V') {i : Fin A.n}
    {i' : Fin A'.n} {y : ℂ}
    (hy : y ∈ A'.halfImage i')
    (hi : (A'.chart i').symm (closedUpperHalfPlaneModel.symm y) ∈ A.dom i) :
    (A.chart i ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y)) : ℂ) ∈ A.halfImage i := by
  obtain ⟨hyU, hy0⟩ := A'.mem_halfImage.1 hy
  refine A.mem_halfImage.2 ⟨?_, ?_⟩
  · rw [closedUpperHalfPlaneModel_symm_coe]
    exact A.mem_image.2 ⟨_, hi, rfl⟩
  have he : (A'.chart i').symm ≫ₕ A.chart i ∈ contDiffGroupoid 1 closedUpperHalfPlaneModel :=
    HasGroupoid.compatible (chart_mem_atlas _ _) (chart_mem_atlas _ _)
  obtain ⟨x, hx, hxz⟩ := A'.mem_image.1 hyU
  have hs : closedUpperHalfPlaneModel.symm y ∈ ((A'.chart i').symm ≫ₕ A.chart i).source := by
    refine ⟨?_, A.dom_subset_chart_source i hi⟩
    rw [← hxz]
    exact (A'.chart i').map_source (A'.dom_subset_chart_source i' hx)
  have hpos := ClosedUpperHalfPlane.im_pos_iff_of_mem_contDiffGroupoid he one_ne_zero hs
  rw [coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hy0.le] at hpos
  exact hpos.1 hy0

/-- The chart transition from chart `i` of `A` to chart `i'` of `A'`, read in `ℂ`, is
differentiable at the interior points of the image of chart `i` lying over the domain of chart
`i'`. -/
private theorem differentiableOn_chart_chart_symm
    (A' : FiniteBundleAtlas ClosedUpperHalfPlane M F' V') (i : Fin A.n) (i' : Fin A'.n) :
    DifferentiableOn ℝ
      (fun z ↦ (A'.chart i' ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)) : ℂ))
      ((A.halfImage i : Set ℂ) ∩
        {z | (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∈ A'.dom i'}) := by
  have h := (contDiffOn_ext_coord_change (I := closedUpperHalfPlaneModel) (n := 1)
    (A'.center i') (A.center i)).differentiableOn one_ne_zero
  refine h.congr_mono (fun z _ ↦ ?_) fun z hz ↦ ?_
  · simp only [Function.comp_apply, extChartAt_coe_symm, extChartAt_coe,
      closedUpperHalfPlaneModel_apply]
  obtain ⟨hzU', hz'⟩ := hz
  obtain ⟨hzU, hz0⟩ := A.mem_halfImage.1 hzU'
  obtain ⟨x, hx, hxz⟩ := A.mem_image.1 hzU
  have hx' : x ∈ (A.chart i).source := A.dom_subset_chart_source i hx
  have hzr : z ∈ range closedUpperHalfPlaneModel := by
    rw [range_closedUpperHalfPlaneModel]; exact hz0.le
  simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage,
    extChartAt_target, extChartAt_source, extChartAt_coe_symm, Function.comp_apply]
  refine ⟨⟨?_, hzr⟩, A'.dom_subset_chart_source i' hz'⟩
  rw [← hxz]
  exact (A.chart i).map_source hx'

/-- **Change of atlas preserves null sets, chartwise.** If a property `P` of points of `ℂ` holds
almost everywhere on the interior of the image of chart `i` of `A`, then almost everywhere on the
interior of the image of chart `i'` of `A'` it holds at the reading in chart `i` of the
corresponding point of `M`, wherever that point lies in the domain of chart `i`. The chart
transition from `A` to `A'` is differentiable on the interiors of the chart images, so it carries
null sets to null sets. -/
theorem ae_restrict_halfImage_chart_symm (A' : FiniteBundleAtlas ClosedUpperHalfPlane M F' V')
    {i : Fin A.n} (i' : Fin A'.n) {P : ℂ → Prop}
    (h : ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ), P z) :
    ∀ᵐ y ∂volume.restrict (A'.halfImage i' : Set ℂ),
      (A'.chart i').symm (closedUpperHalfPlaneModel.symm y) ∈ A.dom i →
        P (A.chart i ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y)) : ℂ) := by
  have hN : volume ({z | ¬P z} ∩ ((A.halfImage i : Set ℂ) ∩
      {z | (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∈ A'.dom i'})) = 0 := by
    rw [ae_iff, Measure.restrict_apply' (A.halfImage i).isOpen.measurableSet] at h
    exact measure_mono_null (inter_subset_inter_right _ inter_subset_left) h
  have himage := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    ((A.differentiableOn_chart_chart_symm A' i i').mono inter_subset_right) hN
  rw [ae_iff, Measure.restrict_apply' (A'.halfImage i').isOpen.measurableSet]
  refine measure_mono_null (fun y hy ↦ ?_) himage
  simp only [mem_inter_iff, mem_ofPred_eq, not_imp] at hy
  obtain ⟨⟨hdom, hP⟩, hyU⟩ := hy
  obtain ⟨hyU', hy0⟩ := A'.mem_halfImage.1 hyU
  have hleft : (A.chart i).symm (closedUpperHalfPlaneModel.symm
      (A.chart i ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y)) : ℂ)) =
        (A'.chart i').symm (closedUpperHalfPlaneModel.symm y) := by
    rw [closedUpperHalfPlaneModel_symm_coe, (A.chart i).left_inv (A.dom_subset_chart_source i hdom)]
  refine ⟨_, ⟨hP, A.coe_chart_mem_halfImage A' hyU hdom, ?_⟩, ?_⟩
  · rw [mem_ofPred_eq, hleft]
    exact A'.symm_mem_dom hyU'
  · obtain ⟨x, hx, hxz⟩ := A'.mem_image.1 hyU'
    have ht : closedUpperHalfPlaneModel.symm y ∈ (A'.chart i').target := by
      rw [← hxz]
      exact (A'.chart i').map_source (A'.dom_subset_chart_source i' hx)
    simp only [hleft, (A'.chart i').right_inv ht, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg
      hy0.le]

/-- **Almost everywhere statements on `M` do not depend on the atlas.** A property of points of `M`
that holds almost everywhere in every chart of `A`, on the interiors of the chart images, holds
almost everywhere in every chart of `A'`. -/
theorem ae_restrict_halfImage_symm_of_ae (A' : FiniteBundleAtlas ClosedUpperHalfPlane M F' V')
    {P : M → Prop}
    (h : ∀ i, ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
      P ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)))
    (i' : Fin A'.n) :
    ∀ᵐ y ∂volume.restrict (A'.halfImage i' : Set ℂ),
      P ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y)) := by
  have hall := ae_all_iff.2 fun i ↦ A.ae_restrict_halfImage_chart_symm A' i' (h i)
  filter_upwards [hall] with y hy
  obtain ⟨i, hi⟩ := A.exists_mem_dom ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y))
  simpa only [closedUpperHalfPlaneModel_symm_coe,
    (A.chart i).left_inv (A.dom_subset_chart_source i hi)] using hy i hi

/-- Sections whose readings agree almost everywhere in every chart of one finite bundle atlas, on
the interiors of the chart images, agree almost everywhere in every chart of any other. -/
theorem halfCoord_ae_eq_of_halfCoord_ae_eq (A' : FiniteBundleAtlas ClosedUpperHalfPlane M F V)
    {s t : ∀ x, V x}
    (h : ∀ i, A.halfCoord i s =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i t)
    (i' : Fin A'.n) :
    A'.halfCoord i' s =ᵐ[volume.restrict (A'.halfImage i' : Set ℂ)] A'.halfCoord i' t := by
  have hst := A.ae_restrict_halfImage_symm_of_ae A' (P := fun x ↦ s x = t x) (fun i ↦ by
    filter_upwards [h i, ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z hz hzU
    rw [halfCoord_def, halfCoord_def] at hz
    exact (A.coord_eq_coord_iff (A.mem_halfImage.1 hzU).1).1 hz) i'
  filter_upwards [hst] with y hy
  simp only [halfCoord_def, coord_def, hy]

end FiniteBundleAtlas

end Measure

section Linear

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

namespace FiniteBundleAtlas

variable (A A' : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

/-- Wherever chart `i'` of `A'` and chart `i` of `A` overlap, the reading of a section in chart
`i'` is the coordinate change of the bundle applied to its reading in chart `i` at the
corresponding point. -/
theorem halfCoord_eq_coordChangeL_halfCoord {i : Fin A.n} {i' : Fin A'.n} (s : ∀ x, V x)
    {y : ℂ} (hj : (A'.chart i').symm (closedUpperHalfPlaneModel.symm y) ∈ (A'.triv i').baseSet)
    (hi : (A'.chart i').symm (closedUpperHalfPlaneModel.symm y) ∈ A.dom i) :
    A'.halfCoord i' s y = (A.triv i).coordChangeL ℝ (A'.triv i')
      ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y))
      (A.halfCoord i s (A.chart i ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y)))) := by
  rw [halfCoord_def, halfCoord_def, closedUpperHalfPlaneModel_symm_coe]
  exact A.coord_eq_coordChangeL_coord A' s hj hi

end FiniteBundleAtlas

end Linear

section Sobolev

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A A' : FiniteBundleAtlas ClosedUpperHalfPlane M F V} {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

namespace BorderedSobolevSection

open FiniteBundleAtlas

/-! ### Chart data and sections -/

/-- Every element of `W^{k,p}(V)` consists of the chartwise components of a section, read in the
charts of `A` as `A.halfCoord i s`. -/
theorem exists_ae_eq_halfCoord (w : BorderedSobolevSection A p k) :
    ∃ s : ∀ x, V x, ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s :=
  (exists_section_memWkpLoc w).imp fun _ h ↦ h.1

/-- **Uniqueness.** Two elements of `W^{k,p}(V)` whose chart data are the readings
`A.halfCoord i s` of the same section are equal. -/
theorem eq_of_ae_eq_halfCoord {w w' : BorderedSobolevSection A p k} {s : ∀ x, V x}
    (hw : ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (hw' : ∀ i, A.halfSectionChartData.chartValueL volume p k i w'
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s) :
    w = w' :=
  SectionChartData.eq_of_ae_eq_coord (s := s)
    (fun i ↦ (hw i).trans (A.halfSectionChartData_coord_ae_eq i s).symm)
    (fun i ↦ (hw' i).trans (A.halfSectionChartData_coord_ae_eq i s).symm)

/-- The chart data of a sum are almost everywhere the readings of the sum of the sections. -/
theorem chartValueL_add_ae_halfCoord {w w' : BorderedSobolevSection A p k} {s t : ∀ x, V x}
    {i : Fin A.n}
    (hs : A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (ht : A.halfSectionChartData.chartValueL volume p k i w'
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i t) :
    A.halfSectionChartData.chartValueL volume p k i (w + w' : BorderedSobolevSection A p k)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i (s + t) :=
  (SectionChartData.chartValueL_add_ae_coord
    (hs.trans (A.halfSectionChartData_coord_ae_eq i s).symm)
    (ht.trans (A.halfSectionChartData_coord_ae_eq i t).symm)).trans
      (A.halfSectionChartData_coord_ae_eq i (s + t))

/-- The chart data of a multiple are almost everywhere the readings of the multiple of the
section. -/
theorem chartValueL_smul_ae_halfCoord (c : ℝ) {w : BorderedSobolevSection A p k} {s : ∀ x, V x}
    {i : Fin A.n}
    (hs : A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s) :
    A.halfSectionChartData.chartValueL volume p k i (c • w : BorderedSobolevSection A p k)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i (c • s) :=
  (SectionChartData.chartValueL_smul_ae_coord c
    (hs.trans (A.halfSectionChartData_coord_ae_eq i s).symm)).trans
      (A.halfSectionChartData_coord_ae_eq i (c • s))

/-! ### Change of atlas -/

variable (A A' p k) in
/-- **Transfer of Sobolev sections between atlases.** Every section whose chart data in the charts
of `A` are those of an element of `W^{k,p}(V)` for `A` also has chart data in the charts of `A'`
that are those of an element of `W^{k,p}(V)` for `A'`. -/
def TransfersTo : Prop :=
  ∀ (w : BorderedSobolevSection A p k) (s : ∀ x, V x),
    (∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s) →
      ∃ w' : BorderedSobolevSection A' p k,
        ∀ i', A'.halfSectionChartData.chartValueL volume p k i' w'
          =ᵐ[volume.restrict (A'.halfImage i' : Set ℂ)] A'.halfCoord i' s

/-- Unfolding `TauCeti.BorderedSobolevSection.TransfersTo`, for establishing and using the
transfer property outside this file. -/
theorem transfersTo_iff : TransfersTo A A' p k ↔
    ∀ (w : BorderedSobolevSection A p k) (s : ∀ x, V x),
      (∀ i, A.halfSectionChartData.chartValueL volume p k i w
        =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s) →
        ∃ w' : BorderedSobolevSection A' p k,
          ∀ i', A'.halfSectionChartData.chartValueL volume p k i' w'
            =ᵐ[volume.restrict (A'.halfImage i' : Set ℂ)] A'.halfCoord i' s :=
  Iff.rfl

theorem transfersTo_refl : TransfersTo A A p k :=
  fun w _ hs ↦ ⟨w, hs⟩

theorem TransfersTo.trans {A'' : FiniteBundleAtlas ClosedUpperHalfPlane M F V}
    (h : TransfersTo A A' p k) (h' : TransfersTo A' A'' p k) : TransfersTo A A'' p k :=
  fun w s hs ↦
    let ⟨w', hw'⟩ := h w s hs
    h' w' s hw'

/-- The element of `W^{k,p}(V)` for `A'` with the same section as `w`, before continuity is
established. -/
private def changeAtlasAux (h : TransfersTo A A' p k) (w : BorderedSobolevSection A p k) :
    BorderedSobolevSection A' p k :=
  (h w _ (exists_ae_eq_halfCoord w).choose_spec).choose

variable [IsManifold closedUpperHalfPlaneModel 1 M]

private theorem chartValueL_changeAtlasAux_ae (h : TransfersTo A A' p k)
    {w : BorderedSobolevSection A p k} {s : ∀ x, V x}
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (i' : Fin A'.n) :
    A'.halfSectionChartData.chartValueL volume p k i' (changeAtlasAux h w)
      =ᵐ[volume.restrict (A'.halfImage i' : Set ℂ)] A'.halfCoord i' s :=
  ((h w _ (exists_ae_eq_halfCoord w).choose_spec).choose_spec i').trans <|
    A.halfCoord_ae_eq_of_halfCoord_ae_eq A'
      (fun i ↦ ((exists_ae_eq_halfCoord w).choose_spec i).symm.trans (hs i)) i'

/-- The element of `W^{k,p}(V)` for `A'` with the same section, as a linear map. -/
private def changeAtlasₗ (h : TransfersTo A A' p k) :
    BorderedSobolevSection A p k →ₗ[ℝ] BorderedSobolevSection A' p k where
  toFun := changeAtlasAux h
  map_add' w w' := by
    obtain ⟨s, hs⟩ := exists_ae_eq_halfCoord w
    obtain ⟨t, ht⟩ := exists_ae_eq_halfCoord w'
    exact eq_of_ae_eq_halfCoord
      (chartValueL_changeAtlasAux_ae h fun i ↦ chartValueL_add_ae_halfCoord (hs i) (ht i))
      fun i' ↦ chartValueL_add_ae_halfCoord (chartValueL_changeAtlasAux_ae h hs i')
        (chartValueL_changeAtlasAux_ae h ht i')
  map_smul' c w := by
    obtain ⟨s, hs⟩ := exists_ae_eq_halfCoord w
    exact eq_of_ae_eq_halfCoord
      (chartValueL_changeAtlasAux_ae h fun i ↦ chartValueL_smul_ae_halfCoord c (hs i))
      fun i' ↦ chartValueL_smul_ae_halfCoord c (chartValueL_changeAtlasAux_ae h hs i')

/-- **The graph of the change of atlas is closed.** If `w m → w` in `W^{k,p}(V)` for `A` and the
corresponding elements for `A'` converge to `v`, then in each chart of `A'` the chart data of `v`
are the readings of the section of `w`, almost everywhere on the part lying over the domain of
chart `i` of `A`. -/
private theorem chartValueL_ae_of_tendsto (h : TransfersTo A A' p k)
    {u : ℕ → BorderedSobolevSection A p k} {w : BorderedSobolevSection A p k}
    {v : BorderedSobolevSection A' p k}
    (hu : Tendsto u atTop (𝓝 w)) (hv : Tendsto (changeAtlasₗ h ∘ u) atTop (𝓝 v))
    {s : ∀ x, V x}
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (i : Fin A.n) (i' : Fin A'.n) :
    ∀ᵐ y ∂volume.restrict (A'.halfImage i' : Set ℂ),
      (A'.chart i').symm (closedUpperHalfPlaneModel.symm y) ∈ A.dom i →
        A'.halfSectionChartData.chartValueL volume p k i' v y = A'.halfCoord i' s y := by
  choose t ht using fun m ↦ exists_ae_eq_halfCoord (u m)
  have hc : Tendsto (fun m ↦ A.halfSectionChartData.chartValueL volume p k i (u m)) atTop
      (𝓝 (A.halfSectionChartData.chartValueL volume p k i w)) :=
    ((A.halfSectionChartData.chartValueL volume p k i).continuous.tendsto _).comp
      ((continuous_subtypeVal.tendsto w).comp hu)
  have hc' : Tendsto (fun m ↦ A'.halfSectionChartData.chartValueL volume p k i'
      (changeAtlasₗ h (u m))) atTop (𝓝 (A'.halfSectionChartData.chartValueL volume p k i' v)) :=
    ((A'.halfSectionChartData.chartValueL volume p k i').continuous.tendsto _).comp
      ((continuous_subtypeVal.tendsto v).comp hv)
  -- Almost everywhere convergence of the chart-`i'` data of the images along a subsequence, then
  -- of the chart-`i` data along a further subsequence.
  obtain ⟨ns, hns, hae'⟩ := (tendstoInMeasure_of_tendsto_Lp hc').exists_seq_tendsto_ae
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp
    (hc.comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  -- In chart `i` of `A`: the chart data are the readings, and they converge along the subsequence.
  have hA : ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
      (∀ m, A.halfSectionChartData.chartValueL volume p k i (u m) z = A.halfCoord i (t m) z) ∧
        Tendsto (fun m ↦ A.halfSectionChartData.chartValueL volume p k i (u (ns (ms m))) z)
          atTop (𝓝 (A.halfCoord i s z)) := by
    filter_upwards [ae_all_iff.2 fun m ↦ ht m i, hae, hs i] with z hz hz' hzs
    exact ⟨hz, hzs ▸ hz'⟩
  have himg : ∀ᵐ y ∂volume.restrict (A'.halfImage i' : Set ℂ), ∀ m,
      A'.halfSectionChartData.chartValueL volume p k i' (changeAtlasₗ h (u m)) y =
        A'.halfCoord i' (t m) y :=
    ae_all_iff.2 fun m ↦ chartValueL_changeAtlasAux_ae h (ht m) i'
  filter_upwards [A.ae_restrict_halfImage_chart_symm A' i' hA, himg, hae',
    ae_restrict_mem (A'.halfImage i').isOpen.measurableSet] with y hy himg hae' hyU hdom
  obtain ⟨hyA, hyT⟩ := hy hdom
  have hyB := A'.dom_subset_baseSet i' (A'.symm_mem_dom (A'.mem_halfImage.1 hyU).1)
  refine tendsto_nhds_unique (hae'.comp hms.tendsto_atTop) ?_
  rw [A.halfCoord_eq_coordChangeL_halfCoord A' s hyB hdom]
  refine ((((A.triv i).coordChangeL ℝ (A'.triv i')
    ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y))).continuous.tendsto _).comp
      hyT).congr fun m ↦ ?_
  simp only [Function.comp_apply]
  rw [himg, hyA, A.halfCoord_eq_coordChangeL_halfCoord A' _ hyB hdom]

/-- **Change of atlas.** Given the transfer property `h` from `A` to `A'`, the continuous linear map
from `W^{k,p}(V)` for `A` to `W^{k,p}(V)` for `A'` sending an element to the element whose chart
data are the readings of the same section
(`TauCeti.BorderedSobolevSection.chartValueL_changeAtlas_ae`). Continuity is the closed graph
theorem. -/
def changeAtlas (h : TransfersTo A A' p k) :
    BorderedSobolevSection A p k →L[ℝ] BorderedSobolevSection A' p k :=
  ContinuousLinearMap.ofSeqClosedGraph (g := changeAtlasₗ h) fun u w v hu hv ↦ by
    obtain ⟨s, hs⟩ := exists_ae_eq_halfCoord w
    refine eq_of_ae_eq_halfCoord (s := s) (fun i' ↦ ?_) (chartValueL_changeAtlasAux_ae h hs)
    filter_upwards [ae_all_iff.2 fun i ↦ chartValueL_ae_of_tendsto h hu hv hs i i'] with y hy
    obtain ⟨i, hi⟩ := A.exists_mem_dom ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y))
    exact hy i hi

/-- The chart data of `changeAtlas h w` are the readings in the charts of `A'` of any section whose
readings in the charts of `A` are the chart data of `w`. -/
theorem chartValueL_changeAtlas_ae (h : TransfersTo A A' p k) {w : BorderedSobolevSection A p k}
    {s : ∀ x, V x}
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (i' : Fin A'.n) :
    A'.halfSectionChartData.chartValueL volume p k i' (changeAtlas h w)
      =ᵐ[volume.restrict (A'.halfImage i' : Set ℂ)] A'.halfCoord i' s :=
  chartValueL_changeAtlasAux_ae h hs i'

/-- **Identification of the change of atlas.** An element `w'` for `A'` whose chart data are the
readings in the charts of `A'` of a section of `w` is the image of `w`. -/
theorem changeAtlas_eq_of_ae_eq_halfCoord (h : TransfersTo A A' p k)
    {w : BorderedSobolevSection A p k} {w' : BorderedSobolevSection A' p k} {s : ∀ x, V x}
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (hs' : ∀ i', A'.halfSectionChartData.chartValueL volume p k i' w'
      =ᵐ[volume.restrict (A'.halfImage i' : Set ℂ)] A'.halfCoord i' s) :
    changeAtlas h w = w' :=
  eq_of_ae_eq_halfCoord (chartValueL_changeAtlas_ae h hs) hs'

theorem changeAtlas_refl_apply (w : BorderedSobolevSection A p k) :
    changeAtlas (transfersTo_refl (A := A) (p := p) (k := k)) w = w := by
  obtain ⟨s, hs⟩ := exists_ae_eq_halfCoord w
  exact changeAtlas_eq_of_ae_eq_halfCoord _ hs hs

@[simp]
theorem changeAtlas_refl :
    changeAtlas (transfersTo_refl (A := A) (p := p) (k := k)) = ContinuousLinearMap.id ℝ _ :=
  ContinuousLinearMap.ext changeAtlas_refl_apply

@[simp]
theorem changeAtlas_changeAtlas {A'' : FiniteBundleAtlas ClosedUpperHalfPlane M F V}
    (h : TransfersTo A A' p k) (h' : TransfersTo A' A'' p k) (w : BorderedSobolevSection A p k) :
    changeAtlas h' (changeAtlas h w) = changeAtlas (h.trans h') w := by
  obtain ⟨s, hs⟩ := exists_ae_eq_halfCoord w
  exact changeAtlas_eq_of_ae_eq_halfCoord h' (chartValueL_changeAtlas_ae h hs)
    (chartValueL_changeAtlas_ae (h.trans h') hs)

@[simp]
theorem changeAtlas_comp {A'' : FiniteBundleAtlas ClosedUpperHalfPlane M F V}
    (h : TransfersTo A A' p k) (h' : TransfersTo A' A'' p k) :
    (changeAtlas h').comp (changeAtlas h) = changeAtlas (h.trans h') :=
  ContinuousLinearMap.ext (changeAtlas_changeAtlas h h')

/-- The change of atlas is injective: two sections with the same readings almost everywhere in the
charts of `A'` have the same readings almost everywhere in the charts of `A`. -/
theorem changeAtlas_injective (h : TransfersTo A A' p k) :
    Function.Injective (changeAtlas h) := by
  intro w v hwv
  obtain ⟨s, hs⟩ := exists_ae_eq_halfCoord w
  obtain ⟨t, ht⟩ := exists_ae_eq_halfCoord v
  have hst := A'.halfCoord_ae_eq_of_halfCoord_ae_eq A fun i' ↦
    (chartValueL_changeAtlas_ae h hs i').symm.trans (hwv ▸ chartValueL_changeAtlas_ae h ht i')
  exact eq_of_ae_eq_halfCoord hs fun i ↦ (ht i).trans (hst i).symm

/-- The change of atlas commutes with forgetting the highest derivative. -/
theorem lowerOrderL_changeAtlas (h : TransfersTo A A' p (k + 1)) (h₀ : TransfersTo A A' p k)
    (w : BorderedSobolevSection A p (k + 1)) :
    A'.halfSectionChartData.lowerOrderL volume p k (changeAtlas h w) =
      changeAtlas h₀ (A.halfSectionChartData.lowerOrderL volume p k w) := by
  obtain ⟨s, hs⟩ := exists_ae_eq_halfCoord w
  refine eq_of_ae_eq_halfCoord (s := s) (fun i' ↦ ?_) (chartValueL_changeAtlas_ae h₀ fun i ↦ ?_)
  · rw [SectionChartData.chartValueL_coe_lowerOrderL]
    exact chartValueL_changeAtlas_ae h hs i'
  · rw [SectionChartData.chartValueL_coe_lowerOrderL]
    exact hs i

/-- The change of atlas sends the Sobolev section of a `Cᵏ` section for `A` to the Sobolev section
of the same `Cᵏ` section for `A'`. -/
@[simp]
theorem changeAtlas_ofContMDiffSection [IsManifold closedUpperHalfPlaneModel k M]
    [ContMDiffVectorBundle k F V closedUpperHalfPlaneModel] (h : TransfersTo A A' p k)
    (s : Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯) :
    changeAtlas h (ofContMDiffSection A p k s) = ofContMDiffSection A' p k s :=
  changeAtlas_eq_of_ae_eq_halfCoord h (chartValueL_ofContMDiffSection_ae A p k s)
    (chartValueL_ofContMDiffSection_ae A' p k s)

/-- **Independence of the atlas.** If sections transfer between `A` and `A'` in both directions,
the Sobolev spaces of sections for the two atlases are isomorphic Banach spaces, an element
corresponding to the element with the same section. In particular their norms are equivalent. -/
def atlasEquiv (h : TransfersTo A A' p k) (h' : TransfersTo A' A p k) :
    BorderedSobolevSection A p k ≃L[ℝ] BorderedSobolevSection A' p k :=
  ContinuousLinearEquiv.ofContinuousLinearMap (changeAtlas h) (changeAtlas h')
    (ContinuousLinearMap.ext fun w ↦
      (changeAtlas_changeAtlas h' h w).trans (changeAtlas_refl_apply w))
    (ContinuousLinearMap.ext fun w ↦
      (changeAtlas_changeAtlas h h' w).trans (changeAtlas_refl_apply w))

@[simp]
theorem toContinuousLinearMap_atlasEquiv (h : TransfersTo A A' p k)
    (h' : TransfersTo A' A p k) :
    (atlasEquiv h h' : BorderedSobolevSection A p k →L[ℝ] BorderedSobolevSection A' p k) =
      changeAtlas h :=
  (rfl)

@[simp]
theorem atlasEquiv_apply (h : TransfersTo A A' p k) (h' : TransfersTo A' A p k)
    (w : BorderedSobolevSection A p k) : atlasEquiv h h' w = changeAtlas h w :=
  (rfl)

theorem atlasEquiv_symm_apply (h : TransfersTo A A' p k) (h' : TransfersTo A' A p k)
    (w : BorderedSobolevSection A' p k) : (atlasEquiv h h').symm w = changeAtlas h' w :=
  (rfl)

@[simp]
theorem atlasEquiv_symm (h : TransfersTo A A' p k) (h' : TransfersTo A' A p k) :
    (atlasEquiv h h').symm = atlasEquiv h' h :=
  ContinuousLinearEquiv.ext (funext fun w ↦ atlasEquiv_symm_apply h h' w)

@[simp]
theorem atlasEquiv_refl :
    atlasEquiv (transfersTo_refl (A := A) (p := p) (k := k)) transfersTo_refl =
      ContinuousLinearEquiv.refl ℝ _ :=
  ContinuousLinearEquiv.ext (funext changeAtlas_refl_apply)

@[simp]
theorem atlasEquiv_trans {A'' : FiniteBundleAtlas ClosedUpperHalfPlane M F V}
    (h₁ : TransfersTo A A' p k) (h₁' : TransfersTo A' A p k) (h₂ : TransfersTo A' A'' p k)
    (h₂' : TransfersTo A'' A' p k) :
    (atlasEquiv h₁ h₁').trans (atlasEquiv h₂ h₂') = atlasEquiv (h₁.trans h₂) (h₂'.trans h₁') :=
  ContinuousLinearEquiv.ext (funext (changeAtlas_changeAtlas h₁ h₂))

/-- **Equivalence of norms.** If sections transfer between `A` and `A'` in both directions, the
norms of the Sobolev spaces of sections for the two atlases are equivalent: there is a positive
constant `C` bounding the norm of each element by `C` times the norm of the element of the other
atlas with the same section. -/
theorem exists_norm_changeAtlas_le (h : TransfersTo A A' p k) (h' : TransfersTo A' A p k) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : BorderedSobolevSection A p k,
      ‖changeAtlas h w‖ ≤ C * ‖w‖ ∧ ‖w‖ ≤ C * ‖changeAtlas h w‖ := by
  set T := changeAtlas h
  set S := changeAtlas h'
  refine ⟨max 1 (max ‖T‖ ‖S‖), lt_max_of_lt_left one_pos, fun w ↦ ⟨(T.le_opNorm w).trans
    (mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_left _ _)) (norm_nonneg w)), ?_⟩⟩
  calc ‖w‖ = ‖S (T w)‖ := by rw [(changeAtlas_changeAtlas _ _ w).trans (changeAtlas_refl_apply w)]
    _ ≤ ‖S‖ * ‖T w‖ := S.le_opNorm _
    _ ≤ max 1 (max ‖T‖ ‖S‖) * ‖T w‖ :=
      mul_le_mul_of_nonneg_right (le_max_of_le_right (le_max_right _ _)) (norm_nonneg _)

end BorderedSobolevSection

end Sobolev

end TauCeti
