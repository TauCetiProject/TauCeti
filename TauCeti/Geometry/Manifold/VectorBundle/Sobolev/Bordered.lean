/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Analysis.Sobolev.Local.Coordinates
public import TauCeti.Geometry.Manifold.Complex.ClosedUpperHalfPlane
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Sobolev.Wkp.Chain
import TauCeti.Analysis.Sobolev.Wkp.Classical
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Sobolev spaces of sections over surfaces with boundary

Let `M` be a `C¹` manifold modelled on the closed upper half-plane `ClosedUpperHalfPlane`, for
instance a surface with boundary, and let `V → M` be a real vector bundle with finite-dimensional
model fibre `F`. This file constructs the Banach space `W^{k,p}(V)` of sections of `V` whose
coordinates in finitely many bundle charts are Sobolev functions of order `k`, for every natural
number `k` and `1 ≤ p ≤ ∞`. It is the analogue for bases with boundary of
`TauCeti.SobolevSection`, which treats boundaryless bases.

The charts are fixed by a finite bundle atlas
`A : TauCeti.FiniteBundleAtlas ClosedUpperHalfPlane M F V`. The image of chart `i` is a relatively
open subset of the closed upper half-plane; in `ℂ` it is `A.halfClosedImage i = Ω ∩ {0 ≤ im}` for
an open set `Ω`, and its interior is the open set
`A.halfImage i = Ω ∩ {0 < im}`. In chart `i` a section `s` is read as the `F`-valued function
`A.halfCoord i s` on `ℂ`. Recording these readings on the interiors `A.halfImage i` gives the
chart data `A.halfSectionChartData`, and the space is the general construction of
`TauCeti.SectionChartData.sobolevSections` for them, with respect to Lebesgue measure: an element
is a tuple of scalar Sobolev functions `w i j ∈ W^{k,p}(A.halfImage i)`, one for each chart and
each basis vector of `F`, that are the components of a single section. The real axis is a
Lebesgue null set, so nothing is lost by recording the components on the interiors of the chart
images.

The general construction gives the cocycle characterization, closedness and the lower-order
inclusion once chart transitions carry null sets to null sets
(`TauCeti.FiniteBundleAtlas.aeTransition_halfSectionChartData`). This needs that chart transitions
carry interior points to interior points
(`TauCeti.ClosedUpperHalfPlane.im_pos_iff_of_mem_contDiffGroupoid`) and are `C¹` on the interiors
of the overlaps (`TauCeti.FiniteBundleAtlas.ae_restrict_halfOverlap_halfTransition`). So the space
is complete (`TauCeti.BorderedSobolevSection.instCompleteSpace`).

A `Cᵏ` section has `Cᵏ` chart coordinates up to the real axis, so their derivatives through order
`k` are bounded on the chart images, which are relatively compact; this gives the injective linear
map `TauCeti.BorderedSobolevSection.ofContMDiffSection` from `Cᵏ` sections, with a norm bound.
Conversely, the chart expression of every element lies in the local Sobolev class
`MemWkpLoc p (A.halfClosedImage i) k`, whose `Lᵖ` bounds reach the real axis
(`TauCeti.BorderedSobolevSection.memWkpLoc_halfCoord`).

## Main definitions

* `TauCeti.FiniteBundleAtlas.halfImage`, `TauCeti.FiniteBundleAtlas.halfClosedImage`: the
  interior in `ℂ` of the image of a chart, and the image itself.
* `TauCeti.FiniteBundleAtlas.halfCoord`: a section read in a chart, as a function on `ℂ`.
* `TauCeti.FiniteBundleAtlas.halfSectionChartData`: the chart data on the interiors of the chart
  images.
* `TauCeti.BorderedSobolevSection A p k`: the Banach space `W^{k,p}(V)`.
* `TauCeti.BorderedSobolevSection.ofContMDiffSection`: `Cᵏ` sections as Sobolev sections.

## Main results

* `TauCeti.FiniteBundleAtlas.aeTransition_halfSectionChartData`: chart transitions preserve null
  sets.
* `TauCeti.BorderedSobolevSection.instCompleteSpace`: completeness.
* `TauCeti.BorderedSobolevSection.norm_ofContMDiffSection_le`,
  `TauCeti.BorderedSobolevSection.ofContMDiffSection_injective`: the norm bound and injectivity of
  the inclusion of `Cᵏ` sections.
* `TauCeti.BorderedSobolevSection.memWkpLoc_halfCoord`,
  `TauCeti.BorderedSobolevSection.exists_section_memWkpLoc`: localization to the local Sobolev
  classes on the chart images, up to the real axis.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Appendix C.1.
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold Topology ENNReal ContDiff

namespace TauCeti

section Atlas

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

namespace FiniteBundleAtlas

variable (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

/-- The interior in `ℂ` of the image of chart `i`: the points of positive imaginary part lying in
the image of the chart. -/
def halfImage (i : Fin A.n) : Opens ℂ :=
  ⟨closedUpperHalfPlaneModel.symm ⁻¹' (A.image i : Set ClosedUpperHalfPlane) ∩
    {z : ℂ | 0 < z.im},
    ((A.image i).isOpen.preimage closedUpperHalfPlaneModel.continuous_symm).inter
      (isOpen_lt continuous_const Complex.continuous_im)⟩

theorem mem_halfImage {i : Fin A.n} {z : ℂ} :
    z ∈ A.halfImage i ↔ closedUpperHalfPlaneModel.symm z ∈ A.image i ∧ 0 < z.im :=
  Iff.rfl

/-- The image of chart `i` in `ℂ`: a relatively open subset of the closed upper half-plane. -/
def halfClosedImage (i : Fin A.n) : Set ℂ :=
  closedUpperHalfPlaneModel.symm ⁻¹' (A.image i : Set ClosedUpperHalfPlane) ∩ {z : ℂ | 0 ≤ z.im}

theorem halfClosedImage_eq_image_val (i : Fin A.n) :
    A.halfClosedImage i = Subtype.val '' (A.image i : Set ClosedUpperHalfPlane) := by
  ext z
  refine ⟨fun ⟨hz, hz0⟩ ↦ ⟨_, hz, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz0⟩, ?_⟩
  rintro ⟨w, hw, rfl⟩
  exact ⟨by simpa using hw, w.2⟩

theorem halfImage_subset_halfClosedImage (i : Fin A.n) :
    (A.halfImage i : Set ℂ) ⊆ A.halfClosedImage i :=
  fun z hz ↦ ⟨hz.1, (show 0 < z.im from hz.2).le⟩

/-- The interior of the image of chart `i` in `ℂ` is `A.halfImage i`. -/
theorem interior_halfClosedImage (i : Fin A.n) :
    Opens.interior (A.halfClosedImage i) = A.halfImage i :=
  Opens.ext <| interior_inter_setOf_im_nonneg
    ((A.image i).isOpen.preimage closedUpperHalfPlaneModel.continuous_symm)

/-- The points of the image of chart `i` in `ℂ` that are not in its interior lie on the real
axis, so the image and its interior differ by a null set. -/
theorem halfClosedImage_ae_le_halfImage (i : Fin A.n) :
    A.halfClosedImage i ≤ᵐ[volume] (A.halfImage i : Set ℂ) :=
  (EventuallyEqSet.inter EventuallyEq.rfl (Complex.setOf_le_im_ae_eq 0)).le

/-- Every point of the image of chart `i` in `ℂ`, including the points on the real axis, is a
limit of points of its interior. -/
theorem halfClosedImage_subset_closure_halfImage (i : Fin A.n) :
    A.halfClosedImage i ⊆ closure (A.halfImage i : Set ℂ) := by
  rintro w ⟨hw, hw0⟩
  have hO : closedUpperHalfPlaneModel.symm ⁻¹' (A.image i : Set ClosedUpperHalfPlane) ∈ 𝓝 w :=
    ((A.image i).isOpen.preimage closedUpperHalfPlaneModel.continuous_symm).mem_nhds hw
  have ht : Tendsto (fun t : ℝ ↦ w + t * Complex.I) (𝓝[>] 0) (𝓝 w) := by
    have : Continuous fun t : ℝ ↦ w + t * Complex.I := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [ht hO, self_mem_nhdsWithin] with t ht ht0
  exact ⟨ht, by simpa using add_pos_of_nonneg_of_pos hw0 ht0⟩

/-- The overlap of the domains of charts `i` and `i'`, read in chart `i'`, at points of positive
imaginary part. -/
def halfOverlap (i i' : Fin A.n) : Set ℂ :=
  closedUpperHalfPlaneModel.symm ⁻¹' A.overlap i i' ∩ {z : ℂ | 0 < z.im}

theorem isOpen_halfOverlap (i i' : Fin A.n) : IsOpen (A.halfOverlap i i') :=
  ((A.isOpen_overlap i i').preimage closedUpperHalfPlaneModel.continuous_symm).inter
    (isOpen_lt continuous_const Complex.continuous_im)

theorem halfOverlap_subset_halfImage (i i' : Fin A.n) :
    A.halfOverlap i i' ⊆ A.halfImage i' :=
  fun _ hz ↦ ⟨A.overlap_subset_image i i' hz.1, hz.2⟩

/-- The chart transition from chart `i'` to chart `i`, as a function on `ℂ`. -/
def halfTransition (i i' : Fin A.n) (z : ℂ) : ℂ :=
  A.transition i i' (closedUpperHalfPlaneModel.symm z)

theorem symm_halfTransition (i i' : Fin A.n) (z : ℂ) :
    closedUpperHalfPlaneModel.symm (A.halfTransition i i' z) =
      A.transition i i' (closedUpperHalfPlaneModel.symm z) :=
  closedUpperHalfPlaneModel_symm_coe _

/-- A point of the closed upper half-plane, read in `ℂ` and transported by a chart transition,
is the chart transition of the point. -/
theorem halfTransition_coe_chart {i i' : Fin A.n} {x : M} (hx : x ∈ A.dom i') :
    A.halfTransition i i' (A.chart i' x : ℂ) = A.chart i x := by
  rw [halfTransition, closedUpperHalfPlaneModel_symm_coe, A.transition_chart hx]

/-- A section read in chart `i`, as a function on `ℂ`. -/
def halfCoord (i : Fin A.n) (s : ∀ x, V x) (z : ℂ) : F :=
  A.coord i s (closedUpperHalfPlaneModel.symm z)

theorem halfCoord_coe_chart {i : Fin A.n} (s : ∀ x, V x) {x : M} (hx : x ∈ A.dom i) :
    A.halfCoord i s (A.chart i x : ℂ) = (A.triv i ⟨x, s x⟩).2 := by
  rw [halfCoord, closedUpperHalfPlaneModel_symm_coe, A.coord_chart s hx]

/-- The points of the target of the extended chart `i`, a relatively open subset of the closed
upper half-plane in `ℂ`, whose preimage lies in the base set of the bundle chart. -/
def halfChartSet (i : Fin A.n) : Set ℂ :=
  (extChartAt closedUpperHalfPlaneModel (A.center i)).target ∩
    (extChartAt closedUpperHalfPlaneModel (A.center i)).symm ⁻¹' (A.triv i).baseSet

theorem uniqueDiffOn_halfChartSet (i : Fin A.n) : UniqueDiffOn ℝ (A.halfChartSet i) :=
  fun z hz ↦ (uniqueDiffOn_extChartAt_target (A.center i) z hz.1).mono_nhds <|
    nhdsWithin_le_iff.2 <| inter_mem self_mem_nhdsWithin <|
      (continuousOn_extChartAt_symm (A.center i) z hz.1).preimage_mem_nhdsWithin
        ((A.triv i).open_baseSet.mem_nhds hz.2)

/-- The image of the closure of the domain of chart `i` in `ℂ`, a compact set. -/
theorem isCompact_extChartAt_image_closure_dom (i : Fin A.n) :
    IsCompact (extChartAt closedUpperHalfPlaneModel (A.center i) '' closure (A.dom i)) :=
  (A.isCompact_closure_dom i).image_of_continuousOn
    ((continuousOn_extChartAt (A.center i)).mono (by
      rw [extChartAt_source]; exact A.closure_dom_subset_source i))

theorem extChartAt_image_closure_dom_subset_halfChartSet (i : Fin A.n) :
    extChartAt closedUpperHalfPlaneModel (A.center i) '' closure (A.dom i) ⊆ A.halfChartSet i := by
  rintro _ ⟨x, hx, rfl⟩
  have hs : x ∈ (extChartAt closedUpperHalfPlaneModel (A.center i)).source := by
    rw [extChartAt_source]; exact A.closure_dom_subset_source i hx
  refine ⟨(extChartAt closedUpperHalfPlaneModel (A.center i)).map_source hs, ?_⟩
  rw [mem_preimage, (extChartAt closedUpperHalfPlaneModel (A.center i)).left_inv hs]
  exact A.closure_dom_subset_baseSet i hx

theorem halfImage_subset_extChartAt_image_closure_dom (i : Fin A.n) :
    (A.halfImage i : Set ℂ) ⊆
      extChartAt closedUpperHalfPlaneModel (A.center i) '' closure (A.dom i) := by
  rintro z ⟨hz, hz0⟩
  obtain ⟨x, hx, hxz⟩ := A.mem_image.1 hz
  refine ⟨x, subset_closure hx, ?_⟩
  rw [extChartAt_coe, Function.comp_apply, closedUpperHalfPlaneModel_apply]
  change (A.chart i x : ℂ) = z
  rw [hxz, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (show 0 < z.im from hz0).le]

theorem halfImage_subset_halfChartSet (i : Fin A.n) :
    (A.halfImage i : Set ℂ) ⊆ A.halfChartSet i :=
  (A.halfImage_subset_extChartAt_image_closure_dom i).trans
    (A.extChartAt_image_closure_dom_subset_halfChartSet i)

variable [IsManifold closedUpperHalfPlaneModel 1 M]

/-- Chart transitions carry interior points of the overlap to interior points. -/
theorem halfTransition_mem_halfOverlap {i i' : Fin A.n} {z : ℂ} (hz : z ∈ A.halfOverlap i i') :
    A.halfTransition i i' z ∈ A.halfOverlap i' i := by
  obtain ⟨hz, hz0⟩ := hz
  obtain ⟨x, hx, hxz⟩ := A.mem_overlap.1 hz
  have hz0 : 0 < z.im := hz0
  have hx' := A.dom_subset_chart_source i' hx.2
  have he : (A.chart i').symm ≫ₕ A.chart i ∈ contDiffGroupoid 1 closedUpperHalfPlaneModel :=
    HasGroupoid.compatible (chart_mem_atlas _ _) (chart_mem_atlas _ _)
  have hs : A.chart i' x ∈ ((A.chart i').symm ≫ₕ A.chart i).source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      mem_inter_iff, mem_preimage, (A.chart i').map_source hx', (A.chart i').left_inv hx',
      true_and]
    exact A.dom_subset_chart_source i hx.1
  have hpos := ClosedUpperHalfPlane.im_pos_iff_of_mem_contDiffGroupoid he one_ne_zero hs
  have hz' : (A.chart i' x : ℂ) = z := by
    rw [hxz, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz0.le]
  refine ⟨?_, ?_⟩
  · rw [mem_preimage, symm_halfTransition]
    exact A.transition_mem_overlap (A.mem_overlap.2 ⟨x, hx, hxz⟩)
  · rw [mem_ofPred_eq, halfTransition, ← hxz, A.transition_chart hx.2]
    have h := hpos.1 (hz' ▸ hz0)
    rwa [OpenPartialHomeomorph.coe_trans, Function.comp_apply, (A.chart i').left_inv hx'] at h

omit [IsManifold closedUpperHalfPlaneModel 1 M] in
theorem halfTransition_halfTransition {i i' : Fin A.n} {z : ℂ} (hz : z ∈ A.halfOverlap i i') :
    A.halfTransition i' i (A.halfTransition i i' z) = z := by
  rw [halfTransition, symm_halfTransition, A.transition_transition hz.1,
    coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (show 0 < z.im from hz.2).le]

/-- Chart transitions are differentiable on the interiors of the overlaps. -/
theorem differentiableOn_halfTransition (i i' : Fin A.n) :
    DifferentiableOn ℝ (A.halfTransition i i') (A.halfOverlap i i') := by
  have h := (contDiffOn_ext_coord_change (I := closedUpperHalfPlaneModel) (n := 1)
    (A.center i) (A.center i')).differentiableOn one_ne_zero
  refine h.congr_mono (fun z hz ↦ ?_) ?_
  · obtain ⟨x, hx, hxz⟩ := A.mem_overlap.1 hz.1
    have hx' : x ∈ (A.chart i').source := A.dom_subset_chart_source i' hx.2
    simp only [halfTransition, Function.comp_apply, extChartAt_coe_symm, extChartAt_coe,
      ← hxz, A.transition_chart hx.2, (A.chart i').left_inv hx', closedUpperHalfPlaneModel_apply]
  rintro z ⟨hz, hz0⟩
  obtain ⟨x, hx, hxz⟩ := A.mem_overlap.1 hz
  have hz0 : 0 < z.im := hz0
  have hx' : x ∈ (A.chart i').source := A.dom_subset_chart_source i' hx.2
  have hzr : z ∈ range closedUpperHalfPlaneModel := by
    rw [range_closedUpperHalfPlaneModel]; exact hz0.le
  simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage,
    extChartAt_target, extChartAt_source, extChartAt_coe_symm, Function.comp_apply]
  refine ⟨⟨?_, hzr⟩, ?_⟩
  · rw [← hxz]; exact (A.chart i').map_source hx'
  · rw [← hxz, (A.chart i').left_inv hx']; exact A.dom_subset_chart_source i hx.1

/-- **Chart transitions preserve null sets.** A property holding almost everywhere on the
interior of the image of chart `i` holds, after composition with the chart transition, almost
everywhere on the interior of the overlap of charts `i` and `i'` read in chart `i'`. -/
theorem ae_restrict_halfOverlap_halfTransition {i i' : Fin A.n} {P : ℂ → Prop}
    (h : ∀ᵐ z ∂volume.restrict (A.halfImage i), P z) :
    ∀ᵐ y ∂volume.restrict (A.halfOverlap i i'), P (A.halfTransition i i' y) := by
  have hN : volume ({z | ¬P z} ∩ A.halfOverlap i' i) = 0 := by
    rw [ae_iff, Measure.restrict_apply' (A.halfImage i).isOpen.measurableSet] at h
    exact measure_mono_null (inter_subset_inter_right _ (A.halfOverlap_subset_halfImage i' i)) h
  have himage := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    ((A.differentiableOn_halfTransition i' i).mono inter_subset_right) hN
  rw [ae_iff, Measure.restrict_apply' (A.isOpen_halfOverlap i i').measurableSet]
  refine measure_mono_null (fun y hy ↦ ?_) himage
  exact ⟨A.halfTransition i i' y, ⟨hy.1, A.halfTransition_mem_halfOverlap hy.2⟩,
    A.halfTransition_halfTransition hy.2⟩

end FiniteBundleAtlas

end Atlas

section Linear

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

namespace FiniteBundleAtlas

variable (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

/-- **The chart coordinates of a `Cᵏ` section are `Cᵏ` up to the boundary**, on the relatively open
subset `A.halfChartSet i` of the closed upper half-plane. -/
theorem contDiffOn_halfCoord {k : ℕ} [IsManifold closedUpperHalfPlaneModel k M]
    [ContMDiffVectorBundle k F V closedUpperHalfPlaneModel] {s : ∀ x, V x}
    (hs : ContMDiff closedUpperHalfPlaneModel (closedUpperHalfPlaneModel.prod 𝓘(ℝ, F)) k
      fun x ↦ TotalSpace.mk' F x (s x))
    (i : Fin A.n) : ContDiffOn ℝ k (A.halfCoord i s) (A.halfChartSet i) := by
  rw [← contMDiffOn_iff_contDiffOn]
  refine (((A.triv i).contMDiffOn_section_baseSet_iff.1 hs.contMDiffOn).comp
    ((contMDiffOn_extChartAt_symm (A.center i)).mono inter_subset_left) fun _ hy ↦ hy.2).congr
      fun y _ ↦ ?_
  rw [halfCoord, coord_def, Function.comp_apply, extChartAt_coe_symm, Function.comp_apply]

/-- On the interior of the overlap of two charts, the coordinates of a section in chart `i'` are
the coordinate change applied to its coordinates in chart `i` at the transition point. -/
theorem halfCoord_eq_coordChange {i i' : Fin A.n} (s : ∀ x, V x) {z : ℂ}
    (hz : z ∈ A.halfOverlap i i') :
    A.halfCoord i' s z = (A.triv i).coordChangeL ℝ (A.triv i')
      ((A.chart i').symm (closedUpperHalfPlaneModel.symm z))
      (A.halfCoord i s (A.halfTransition i i' z)) := by
  rw [halfCoord, halfCoord, symm_halfTransition]
  exact A.coord_eq_coordChange s hz.1

/-- The chart data of a finite bundle atlas over a base with boundary: a section is read in chart
`i` as `A.halfCoord i s` on the interior `A.halfImage i` of the image of the chart in `ℂ`. At each
point the gluing of a family of functions is read off from the function of any chart containing
the point. -/
@[expose] def halfSectionChartData : SectionChartData ℂ F (∀ x, V x) where
  n := A.n
  image := A.halfImage
  overlap := A.halfOverlap
  isOpen_overlap := A.isOpen_halfOverlap
  overlap_subset_image := A.halfOverlap_subset_halfImage
  transition := A.halfTransition
  coordChange i i' z :=
    (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm (closedUpperHalfPlaneModel.symm z))
  coord := A.halfCoord
  coord_add i s t _ hz := by
    simp only [halfCoord]; exact A.coord_add i s t (A.mem_halfImage.1 hz).1
  coord_smul i c s _ hz := by
    simp only [halfCoord]; exact A.coord_smul i c s (A.mem_halfImage.1 hz).1
  coord_eq_coordChange _ _ s _ hz := A.halfCoord_eq_coordChange s hz
  exists_glue f := by
    classical
    let idx : M → Fin A.n := fun x ↦ (A.exists_mem_dom x).choose
    have hidx (x : M) : x ∈ A.dom (idx x) := (A.exists_mem_dom x).choose_spec
    refine ⟨fun x ↦ (A.triv (idx x)).symm x (f (idx x) (A.chart (idx x) x : ℂ)),
      fun i' z hz ↦ ?_⟩
    obtain ⟨hzU, hz0⟩ := hz
    obtain ⟨x, hx, hxz⟩ := A.mem_image.1 hzU
    have hz0 : 0 < z.im := hz0
    have hz' : z = (A.chart i' x : ℂ) := by
      rw [hxz, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz0.le]
    have hov : z ∈ A.halfOverlap (idx x) i' :=
      ⟨by rw [mem_preimage, ← hxz]; exact A.chart_mem_overlap (hidx x) hx, hz0⟩
    refine ⟨idx x, hov, ?_⟩
    rw [A.halfCoord_eq_coordChange _ hov, hz', A.halfTransition_coe_chart hx,
      A.halfCoord_coe_chart _ (hidx x),
      (A.triv (idx x)).apply_mk_symm (A.dom_subset_baseSet _ (hidx x))]
    rfl

end FiniteBundleAtlas

end Linear

section Sobolev

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

variable (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- **Chart transitions preserve null sets** on the interiors of the chart images. -/
theorem FiniteBundleAtlas.aeTransition_halfSectionChartData
    [IsManifold closedUpperHalfPlaneModel 1 M] : A.halfSectionChartData.AETransition volume :=
  fun _ _ _ h ↦ A.ae_restrict_halfOverlap_halfTransition h

variable [FiniteDimensional ℝ F]

/-- The Sobolev space `W^{k,p}(V)` of sections of `V` over a base with boundary, with respect to
the finite bundle atlas `A`: the tuples of chartwise Sobolev components of sections on the
interiors of the chart images, with the maximum of the component norms. -/
abbrev BorderedSobolevSection : Type :=
  A.halfSectionChartData.sobolevSections volume p k

/-- **Completeness.** The Sobolev space of sections of a vector bundle over a base with boundary
is a Banach space. -/
instance BorderedSobolevSection.instCompleteSpace [IsManifold closedUpperHalfPlaneModel 1 M] :
    CompleteSpace (BorderedSobolevSection A p k) :=
  SectionChartData.completeSpace_sobolevSections A.aeTransition_halfSectionChartData

end Sobolev

section Smooth

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

namespace BorderedSobolevSection

open FiniteBundleAtlas

variable [IsManifold closedUpperHalfPlaneModel k M]
  [ContMDiffVectorBundle k F V closedUpperHalfPlaneModel]

/-- The `j`th component of the chart coordinates of a `Cᵏ` section is `Cᵏ` up to the boundary. -/
private theorem contDiffOn_coord_halfCoord (s : Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯)
    (i : Fin A.n) (j : Fin (finrank ℝ F)) :
    ContDiffOn ℝ k (fun z ↦ (finBasis ℝ F).coord j (A.halfCoord i s z)) (A.halfChartSet i) :=
  (LinearMap.toContinuousLinearMap ((finBasis ℝ F).coord j)).contDiff.comp_contDiffOn
    (A.contDiffOn_halfCoord s.contMDiff i)

/-- The component of the chart coordinates of a `Cᵏ` section along the `j`th vector of the basis
`Module.finBasis ℝ F` is a `W^{k,p}` function on the interior of the image of chart `i`: its
classical derivatives extend continuously to the compact image of the closure of the chart domain,
so they are bounded. -/
private theorem exists_value_ae_eq_halfCoord (s : Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯)
    (i : Fin A.n) (j : Fin (finrank ℝ F)) :
    ∃ w : Wkp volume (A.halfImage i) p k, (Wkp.value k w : ℂ → ℝ)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        fun z ↦ (finBasis ℝ F).coord j (A.halfCoord i s z) := by
  have hf := contDiffOn_coord_halfCoord A k s i j
  refine Wkp.exists_value_ae_eq_of_contDiffOn k (hf.mono (A.halfImage_subset_halfChartSet i))
    fun l hl ↦ ?_
  have hc := hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hl)
    (A.uniqueDiffOn_halfChartSet i)
  have hK := hc.mono (A.extChartAt_image_closure_dom_subset_halfChartSet i)
  refine (hK.memLp_restrict_of_subset_isCompact (A.isCompact_extChartAt_image_closure_dom i)
    (A.halfImage i).isOpen.measurableSet (A.halfImage_subset_extChartAt_image_closure_dom i)
    p).ae_eq ?_
  filter_upwards [ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z hz
  refine iteratedFDerivWithin_eq_iteratedFDeriv (A.uniqueDiffOn_halfChartSet i)
    ((hf.contDiffAt (mem_of_superset ((A.halfImage i).isOpen.mem_nhds hz)
      (A.halfImage_subset_halfChartSet i))).of_le (by exact_mod_cast hl))
    (A.halfImage_subset_halfChartSet i hz)

/-- **`Cᵏ` sections are Sobolev sections.** The linear map sending a `Cᵏ` section `s` of `V` to the
element of `W^{k,p}(V)` whose components in chart `i` are the components of `A.halfCoord i s` in
the basis `Module.finBasis ℝ F`. -/
def ofContMDiffSection :
    Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯ →ₗ[ℝ] BorderedSobolevSection A p k :=
  A.halfSectionChartData.ofComponents volume p k
    { toFun := fun s ↦ s, map_add' := ContMDiffSection.coe_add,
      map_smul' := ContMDiffSection.coe_smul }
    (exists_value_ae_eq_halfCoord A p k)

/-- **Norm bound.** The norm of the Sobolev section of a `Cᵏ` section `s` is at most the sum, over
all charts `i` and basis vectors `j`, of the `Lᵖ` norms on `A.halfImage i` of the classical
derivatives of orders `0` through `k` of the components of `A.halfCoord i s`. -/
theorem norm_ofContMDiffSection_le (s : Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯) :
    ‖ofContMDiffSection A p k s‖ ≤ ∑ i, ∑ j, ∑ l ∈ Finset.range (k + 1),
      lpNorm (iteratedFDeriv ℝ l fun z ↦ (finBasis ℝ F).coord j (A.halfCoord i s z)) p
        (volume.restrict (A.halfImage i : Set ℂ)) :=
  A.halfSectionChartData.norm_le_sum_of_norm_le volume p k fun i j ↦
    Wkp.norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn k _
      ((contDiffOn_coord_halfCoord A k s i j).mono (A.halfImage_subset_halfChartSet i))
      (A.halfSectionChartData.value_ofComponents_ae volume p k _ _ s i j)

/-- **Injectivity.** A `Cᵏ` section whose Sobolev section vanishes is zero: its chart coordinates
vanish almost everywhere on the interiors of the chart images, hence everywhere there by
continuity, and hence also on the real axis, whose points are limits of interior points. -/
theorem ofContMDiffSection_injective : Function.Injective (ofContMDiffSection A p k) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs ↦ ContMDiffSection.ext fun x ↦ ?_
  obtain ⟨i, hx⟩ := A.exists_mem_dom x
  have hcont : ContinuousOn (A.halfCoord i s) (A.halfChartSet i) :=
    (A.contDiffOn_halfCoord s.contMDiff i).continuousOn
  -- The chart data of the zero tuple vanish, so `A.halfCoord i s` vanishes almost everywhere.
  have h0 : A.halfSectionChartData.chartValueL volume p k i
      (ofContMDiffSection A p k s : A.halfSectionChartData.SobolevData volume p k) = 0 := by
    rw [hs, ZeroMemClass.coe_zero, map_zero]
  have hz := Lp.coeFn_zero F p (volume.restrict (A.halfSectionChartData.image i : Set ℂ))
  rw [← h0] at hz
  have hae : A.halfCoord i s =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] fun _ ↦ 0 :=
    (A.halfSectionChartData.chartValueL_ofComponents_ae volume p k _ _ s i).symm.trans hz
  have hzero : EqOn (A.halfCoord i s) 0 (A.halfImage i) :=
    Measure.eqOn_open_of_ae_eq hae (A.halfImage i).isOpen
      (hcont.mono (A.halfImage_subset_halfChartSet i)) continuousOn_const
  -- The point `chart i x` of `ℂ` is a limit of interior points of the chart image.
  have hmem : (A.chart i x : ℂ) ∈ A.halfClosedImage i := by
    rw [halfClosedImage_eq_image_val]
    exact mem_image_of_mem _ (A.mem_image.2 ⟨x, hx, rfl⟩)
  have hK : (A.chart i x : ℂ) ∈ A.halfChartSet i :=
    A.extChartAt_image_closure_dom_subset_halfChartSet i ⟨x, subset_closure hx, by simp [chart]⟩
  have hcl := ((hcont (A.chart i x : ℂ) hK).mono
    (A.halfImage_subset_halfChartSet i)).mem_closure_image
      (A.halfClosedImage_subset_closure_halfImage i hmem)
  have himage : A.halfCoord i s '' (A.halfImage i) ⊆ {0} := by
    rintro _ ⟨z, hz, rfl⟩
    exact hzero hz
  have hval := closure_mono himage hcl
  rw [closure_singleton, mem_singleton_iff, A.halfCoord_coe_chart s hx] at hval
  have hb := A.dom_subset_baseSet i hx
  rw [ContMDiffSection.coe_zero, Pi.zero_apply,
    ← ((A.triv i).continuousLinearEquivAt ℝ x hb).map_eq_zero_iff]
  exact hval

end BorderedSobolevSection

end Smooth

section Localization

/-! ### Localization to the local Sobolev classes up to the boundary -/

variable {U : Set ℂ} {O : Opens ℂ} {p : ℝ≥0∞}

/-- An `Lᵖ` function on an open set `O` that differs from `U` by a null set is locally `Lᵖ` on
`U`, including on compact sets reaching the points of `U` outside `O`. -/
private theorem memLpLoc_of_memLp_of_ae_le {G : Type*} [NormedAddCommGroup G] {f : ℂ → G}
    (hUO : U ≤ᵐ[volume] (O : Set ℂ)) (hf : MemLp f p (volume.restrict O)) : MemLpLoc p U f :=
  memLpLoc_iff.2 fun _ hK _ ↦
    hf.mono_measure (Measure.restrict_mono_ae (EventuallyLE.trans (Eventually.of_forall hK) hUO))

/-- A chain of iterated gradients `G j, …, G n` on the interior `O` of `U`, each the weak
derivative of the previous one and each `Lᵖ` on `O`, gives local Sobolev classes on `U`. -/
private theorem memWkpLoc_of_chain (hO : Opens.interior U = O) (hUO : U ≤ᵐ[volume] (O : Set ℂ))
    {n : ℕ} {G : (l : ℕ) → ℂ → IteratedGradient ℂ l}
    (hG : ∀ l < n, HasWeakFDerivOn volume O (G l) (G (l + 1)))
    (hGp : ∀ l ≤ n, MemLp (G l) p (volume.restrict O)) :
    ∀ m j, j + m ≤ n → MemWkpLoc p U m (G j)
  | 0, j, h => memWkpLoc_zero_iff.2 (memLpLoc_of_memLp_of_ae_le hUO (hGp j (by omega)))
  | m + 1, j, h => memWkpLoc_succ_iff.2 ⟨memLpLoc_of_memLp_of_ae_le hUO (hGp j (by omega)),
      G (j + 1), hO ▸ hG j (by omega), memWkpLoc_of_chain hO hUO hG hGp m (j + 1) (by omega)⟩

variable [Fact (1 ≤ p)]

/-- **Sobolev functions on the interior are locally Sobolev up to the boundary.** If `U` differs
from its interior `O` by a null set, every element of `W^{k,p}(O)` lies in the local Sobolev class
`MemWkpLoc p U k`, whose `Lᵖ` bounds are taken on compact subsets of `U`. -/
private theorem memWkpLoc_value_of_ae_le (hO : Opens.interior U = O)
    (hUO : U ≤ᵐ[volume] (O : Set ℂ)) : ∀ (k : ℕ) (v : Wkp volume O p k),
      MemWkpLoc p U k (Wkp.value k v : ℂ → ℝ)
  | 0, v => memWkpLoc_zero_iff.2 (memLpLoc_of_memLp_of_ae_le hUO (Lp.memLp _))
  | n + 1, v => by
    obtain ⟨G, h0, hG, hGp, -⟩ := Wkp.exists_iteratedGradient_chain n v
    exact memWkpLoc_succ_iff.2 ⟨memLpLoc_of_memLp_of_ae_le hUO (Lp.memLp _), _, hO ▸ h0,
      (memWkpLoc_of_chain hO hUO hG hGp n 0 (by omega)).clm_comp (innerSL ℝ (E := ℂ))⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ClosedUpperHalfPlane M F V} {k : ℕ}

namespace BorderedSobolevSection

open FiniteBundleAtlas

/-- The components of the chart data of a tuple of Sobolev functions are the values of its
entries: if the chart data in chart `i` agree with `A.halfCoord i s`, then the `j`th component of
`A.halfCoord i s` in the basis `Module.finBasis ℝ F` is the value of the entry `w i j`, almost
everywhere on `A.halfImage i`. -/
private theorem value_ae_eq_repr_halfCoord {w : A.halfSectionChartData.SobolevData volume p k}
    {s : ∀ x, V x} {i : Fin A.n}
    (hs : A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (j : Fin (finrank ℝ F)) :
    (Wkp.value k (w i j) : ℂ → ℝ) =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
      fun z ↦ (finBasis ℝ F).repr (A.halfCoord i s z) j := by
  filter_upwards [A.halfSectionChartData.chartValueL_apply_ae volume p k i w, hs] with y hy hy'
  rw [← hy', hy, (finBasis ℝ F).repr_sum_self]

/-- **Localization up to the boundary.** If the chart data of an element `w` of `W^{k,p}(V)` are
the coordinates of the section `s`, then in every chart `i` the chart expression `A.halfCoord i s`
lies in the local Sobolev class `MemWkpLoc p (A.halfClosedImage i) k` on the image of the chart in
the closed upper half-plane, with `Lᵖ` bounds on compact sets reaching the real axis. -/
theorem memWkpLoc_halfCoord (w : BorderedSobolevSection A p k) {s : ∀ x, V x}
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (i : Fin A.n) : MemWkpLoc p (A.halfClosedImage i) k (A.halfCoord i s) :=
  (finBasis ℝ F).memWkpLoc_iff.2 fun j ↦
    (memWkpLoc_value_of_ae_le (A.interior_halfClosedImage i) (A.halfClosedImage_ae_le_halfImage i)
      k _).congr_ae (ae_mono (Measure.restrict_mono_ae (A.halfClosedImage_ae_le_halfImage i))
        (value_ae_eq_repr_halfCoord (hs i) j))

/-- **Localization up to the boundary.** Every element of `W^{k,p}(V)` consists of the components
of a section whose chart expression in every chart `i` lies in the local Sobolev class
`MemWkpLoc p (A.halfClosedImage i) k`. -/
theorem exists_section_memWkpLoc (w : BorderedSobolevSection A p k) :
    ∃ s : ∀ x, V x, (∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s) ∧
        ∀ i, MemWkpLoc p (A.halfClosedImage i) k (A.halfCoord i s) := by
  obtain ⟨s, hs⟩ := A.halfSectionChartData.exists_section volume p k w
  exact ⟨s, hs, memWkpLoc_halfCoord w hs⟩

end BorderedSobolevSection

end Localization

end TauCeti
