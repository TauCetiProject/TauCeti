/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import TauCeti.Analysis.Sobolev.Local.Coordinates
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Geometry.Manifold.Complex.ClosedUpperHalfPlane
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Sobolev.Wkp.Chain
import TauCeti.Analysis.Sobolev.Wkp.Classical

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
`A.halfCoord i s` on `ℂ`. Fixing a basis of `F`, an element of the space is a tuple of scalar
Sobolev functions `w i j ∈ W^{k,p}(A.halfImage i)` with respect to Lebesgue measure, one for each
chart and each basis vector, that are the components of a single section: there is a section `s`
with `A.halfChartValueL p k i w = A.halfCoord i s` almost everywhere on `A.halfImage i` for every
`i`. These tuples form the submodule `TauCeti.borderedSobolevSections A p k` of the finite product
of scalar Sobolev spaces, and `TauCeti.BorderedSobolevSection A p k` carries the product norm. The
real axis is a Lebesgue null set, so nothing is lost by recording the components on the interiors
of the chart images.

Being the components of a section is equivalent to the cocycle relation on every overlap
(`TauCeti.FiniteBundleAtlas.mem_borderedSobolevSections_iff_forall_halfCompatible`). Reading the
relation off from a section needs that chart transitions carry interior points to interior points
(`TauCeti.ClosedUpperHalfPlane.im_pos_iff_of_mem_contDiffGroupoid`) and, being `C¹` on the
interiors of the overlaps, carry null sets to null sets
(`TauCeti.FiniteBundleAtlas.ae_restrict_halfOverlap_halfTransition`). Each relation is closed, so
the space is complete (`TauCeti.BorderedSobolevSection.instCompleteSpace`).

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
* `TauCeti.FiniteBundleAtlas.halfChartValueL`: the `F`-valued `Lᵖ` function on `A.halfImage i`
  assembled from the chart-`i` Sobolev components of a tuple.
* `TauCeti.borderedSobolevSections A p k`: the tuples of chartwise components of sections.
* `TauCeti.BorderedSobolevSection A p k`: the Banach space `W^{k,p}(V)`.
* `TauCeti.BorderedSobolevSection.lowerOrderL`: the inclusion `W^{k+1,p}(V) → W^{k,p}(V)`.
* `TauCeti.BorderedSobolevSection.ofContMDiffSection`: `Cᵏ` sections as Sobolev sections.

## Main results

* `TauCeti.FiniteBundleAtlas.mem_borderedSobolevSections_iff_forall_halfCompatible`: a tuple
  consists of the components of a section exactly when its chart data satisfy the cocycle
  relations.
* `TauCeti.isClosed_borderedSobolevSections`, `TauCeti.BorderedSobolevSection.instCompleteSpace`:
  completeness.
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

/-- The real axis is a Lebesgue null set in `ℂ`. -/
private theorem volume_setOf_im_eq_zero : volume {z : ℂ | z.im = 0} = 0 := by
  have h := Measure.addHaar_submodule (volume : Measure ℂ) (LinearMap.ker Complex.imLm) fun h ↦ by
    have : Complex.I ∈ LinearMap.ker Complex.imLm := h ▸ Submodule.mem_top
    simp at this
  have hker : (LinearMap.ker Complex.imLm : Set ℂ) = {z : ℂ | z.im = 0} := by ext z; simp
  rwa [hker] at h

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
    A.halfClosedImage i ≤ᵐ[volume] (A.halfImage i : Set ℂ) := by
  refine ae_le_set.2 (measure_mono_null (fun z hz ↦ ?_) volume_setOf_im_eq_zero)
  exact le_antisymm (not_lt.1 fun h ↦ hz.2 ⟨hz.1.1, h⟩) hz.1.2

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

theorem halfCoord_add (i : Fin A.n) (s t : ∀ x, V x) {z : ℂ} (hz : z ∈ A.halfImage i) :
    A.halfCoord i (s + t) z = A.halfCoord i s z + A.halfCoord i t z :=
  A.coord_add i s t hz.1

theorem halfCoord_smul (i : Fin A.n) (c : ℝ) (s : ∀ x, V x) {z : ℂ} (hz : z ∈ A.halfImage i) :
    A.halfCoord i (c • s) z = c • A.halfCoord i s z :=
  A.coord_smul i c s hz.1

theorem halfCoord_zero (i : Fin A.n) {z : ℂ} (hz : z ∈ A.halfImage i) :
    A.halfCoord i (0 : ∀ x, V x) z = 0 :=
  A.coord_zero i hz.1

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

end FiniteBundleAtlas

end Linear

section Sobolev

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

variable (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V) (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

/-- Tuples of scalar Sobolev functions of order `k`, one on the interior of the image of each chart
for each vector of the standard basis `Module.finBasis ℝ F` of the model fibre. -/
abbrev BorderedSobolevData : Type :=
  ∀ (i : Fin A.n) (_ : Fin (finrank ℝ F)), Wkp volume (A.halfImage i) p k

namespace FiniteBundleAtlas

/-- The `F`-valued `Lᵖ` function on the interior of the image of chart `i` whose components in the
basis `Module.finBasis ℝ F` are the values of the chart-`i` entries of a tuple of Sobolev
functions. -/
def halfChartValueL (i : Fin A.n) :
    BorderedSobolevData A p k →L[ℝ] Lp F p (volume.restrict (A.halfImage i : Set ℂ)) :=
  ∑ j, ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j)).compLpL p _).comp
    ((Wkp.valueL k).comp ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (finrank ℝ F) ↦ Wkp volume (A.halfImage i) p k) j).comp
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun i : Fin A.n ↦ ∀ _ : Fin (finrank ℝ F), Wkp volume (A.halfImage i) p k) i)))

omit [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- Almost everywhere on the interior of the image of chart `i`, the chart data of a tuple are the
combination of the basis vectors of `F` with the values of its chart-`i` components. -/
theorem halfChartValueL_apply_ae (i : Fin A.n) (w : BorderedSobolevData A p k) :
    ∀ᵐ z ∂volume.restrict (A.halfImage i : Set ℂ),
      A.halfChartValueL p k i w z = ∑ j, Wkp.value k (w i j) z • finBasis ℝ F j := by
  have heq : A.halfChartValueL p k i w = ∑ j,
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j)).compLpL p _
        (Wkp.value k (w i j)) := by
    simp [halfChartValueL]
  have hsum := Lp.coeFn_finsetSum (μ := volume.restrict (A.halfImage i : Set ℂ)) (p := p)
    Finset.univ fun j ↦ (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (finBasis ℝ F j)).compLpL p _ (Wkp.value k (w i j))
  have hj (j : Fin (finrank ℝ F)) := ContinuousLinearMap.coeFn_compLpL (p := p)
    (μ := volume.restrict (A.halfImage i : Set ℂ))
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j)) (Wkp.value k (w i j))
  filter_upwards [hsum, ae_all_iff.2 hj] with y hy hy'
  rw [heq, hy, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ ↦ by simp [hy' j]

omit [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- Forgetting the highest derivative of every component does not change the chart data. -/
theorem halfChartValueL_lowerOrderL (i : Fin A.n) (w : BorderedSobolevData A p (k + 1)) :
    A.halfChartValueL p k i (fun i j ↦ Wkp.lowerOrderL k (w i j)) =
      A.halfChartValueL p (k + 1) i w := by
  simp only [halfChartValueL, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Wkp.valueL_apply, Wkp.valueL_apply, Wkp.value_succ, Wkp.lowerOrderL_apply]

/-- The chart-`i'` data of a tuple are related to its chart-`i` data by the coordinate change of
the bundle on the interior of the overlap of the two charts, almost everywhere. -/
def HalfCompatible (w : BorderedSobolevData A p k) (i i' : Fin A.n) : Prop :=
  ∀ᵐ z ∂volume.restrict (A.halfOverlap i i'), A.halfChartValueL p k i' w z =
    (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm (closedUpperHalfPlaneModel.symm z))
      (A.halfChartValueL p k i w (A.halfTransition i i' z))

theorem halfCompatible_iff {w : BorderedSobolevData A p k} {i i' : Fin A.n} :
    A.HalfCompatible p k w i i' ↔ ∀ᵐ z ∂volume.restrict (A.halfOverlap i i'),
      A.halfChartValueL p k i' w z = (A.triv i).coordChangeL ℝ (A.triv i')
        ((A.chart i').symm (closedUpperHalfPlaneModel.symm z))
        (A.halfChartValueL p k i w (A.halfTransition i i' z)) :=
  Iff.rfl

end FiniteBundleAtlas

open FiniteBundleAtlas

/-- The tuples of chartwise Sobolev components of sections of `V` over a base with boundary: a
tuple `w` belongs to it when some section `s` has, in every chart `i`, coordinates equal almost
everywhere on `A.halfImage i` to the function assembled from the chart-`i` components of `w`. -/
def borderedSobolevSections : Submodule ℝ (BorderedSobolevData A p k) where
  carrier := {w | ∃ s : ∀ x, V x, ∀ i,
    A.halfChartValueL p k i w =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s}
  add_mem' {w w'} := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s + t, fun i ↦ ?_⟩
    filter_upwards [hs i, ht i, ae_restrict_mem (A.halfImage i).isOpen.measurableSet,
      Lp.coeFn_add (A.halfChartValueL p k i w) (A.halfChartValueL p k i w')]
      with y hy ht hyU hadd
    rw [map_add, hadd, Pi.add_apply, hy, ht, A.halfCoord_add i s t hyU]
  zero_mem' := ⟨0, fun i ↦ by
    filter_upwards [ae_restrict_mem (A.halfImage i).isOpen.measurableSet,
      Lp.coeFn_zero F p (volume.restrict (A.halfImage i : Set ℂ))] with y hyU h0
    rw [map_zero, h0, Pi.zero_apply, A.halfCoord_zero i hyU]⟩
  smul_mem' c w := by
    rintro ⟨s, hs⟩
    refine ⟨c • s, fun i ↦ ?_⟩
    filter_upwards [hs i, ae_restrict_mem (A.halfImage i).isOpen.measurableSet,
      Lp.coeFn_smul c (A.halfChartValueL p k i w)] with y hy hyU hsmul
    rw [map_smul, hsmul, Pi.smul_apply, hy, A.halfCoord_smul i c s hyU]

theorem mem_borderedSobolevSections_iff {w : BorderedSobolevData A p k} :
    w ∈ borderedSobolevSections A p k ↔ ∃ s : ∀ x, V x, ∀ i,
      A.halfChartValueL p k i w =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s :=
  Iff.rfl

namespace FiniteBundleAtlas

variable {A p k}

/-- The components of a section satisfy the cocycle relation on every overlap. -/
theorem halfCompatible_of_mem [IsManifold closedUpperHalfPlaneModel 1 M]
    {w : BorderedSobolevData A p k} (hw : w ∈ borderedSobolevSections A p k) (i i' : Fin A.n) :
    A.HalfCompatible p k w i i' := by
  obtain ⟨s, hs⟩ := hw
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (A.halfOverlap_subset_halfImage i i')
    (hs i'), A.ae_restrict_halfOverlap_halfTransition (i' := i') (hs i),
    ae_restrict_mem (A.isOpen_halfOverlap i i').measurableSet] with y h' h hy
  rw [h', h, A.halfCoord_eq_coordChange s hy]

/-- **Gluing.** Chart data satisfying the cocycle relation on every overlap are the components of
a section. At each point the section is read off from the data of any chart containing it. -/
theorem mem_borderedSobolevSections_of_forall_halfCompatible {w : BorderedSobolevData A p k}
    (hw : ∀ i i', A.HalfCompatible p k w i i') : w ∈ borderedSobolevSections A p k := by
  classical
  let idx : M → Fin A.n := fun x ↦ (A.exists_mem_dom x).choose
  have hidx (x : M) : x ∈ A.dom (idx x) := (A.exists_mem_dom x).choose_spec
  let s : ∀ x, V x := fun x ↦
    (A.triv (idx x)).symm x (A.halfChartValueL p k (idx x) w (A.chart (idx x) x : ℂ))
  refine ⟨s, fun i' ↦ ?_⟩
  have hall : ∀ᵐ z ∂volume.restrict (A.halfImage i' : Set ℂ), ∀ i, z ∈ A.halfOverlap i i' →
      A.halfChartValueL p k i' w z = (A.triv i).coordChangeL ℝ (A.triv i')
        ((A.chart i').symm (closedUpperHalfPlaneModel.symm z))
        (A.halfChartValueL p k i w (A.halfTransition i i' z)) := by
    rw [ae_all_iff]
    intro i
    exact ae_restrict_of_ae
      ((ae_restrict_iff' (A.isOpen_halfOverlap i i').measurableSet).1 (hw i i'))
  filter_upwards [hall, ae_restrict_mem (A.halfImage i').isOpen.measurableSet] with z hz hzU
  obtain ⟨hzU, hz0⟩ := hzU
  obtain ⟨x, hx, hxz⟩ := A.mem_image.1 hzU
  have hz0 : 0 < z.im := hz0
  have hxi := hidx x
  have hz' : z = (A.chart i' x : ℂ) := by
    rw [hxz, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz0.le]
  have hov : z ∈ A.halfOverlap (idx x) i' :=
    ⟨by rw [mem_preimage, ← hxz]; exact A.chart_mem_overlap hxi hx, hz0⟩
  rw [hz (idx x) hov, A.halfCoord_eq_coordChange s hov, hz', A.halfTransition_coe_chart hx,
    A.halfCoord_coe_chart s hxi]
  simp only [s]
  rw [(A.triv (idx x)).apply_mk_symm (A.dom_subset_baseSet _ hxi)]

variable [IsManifold closedUpperHalfPlaneModel 1 M]

/-- A tuple consists of the chartwise Sobolev components of a section exactly when its chart data
satisfy the cocycle relation on every overlap. -/
theorem mem_borderedSobolevSections_iff_forall_halfCompatible {w : BorderedSobolevData A p k} :
    w ∈ borderedSobolevSections A p k ↔ ∀ i i', A.HalfCompatible p k w i i' :=
  ⟨halfCompatible_of_mem, mem_borderedSobolevSections_of_forall_halfCompatible⟩

/-- Each cocycle relation is a closed condition on tuples of Sobolev functions: convergence in
`Lᵖ` gives almost everywhere convergence along a subsequence. -/
theorem isClosed_setOf_halfCompatible (i i' : Fin A.n) :
    IsClosed {w : BorderedSobolevData A p k | A.HalfCompatible p k w i i'} := by
  refine IsSeqClosed.isClosed fun {w w₀} hw hlim ↦ ?_
  have hc (j : Fin A.n) : Tendsto (fun m ↦ A.halfChartValueL p k j (w m)) atTop
      (𝓝 (A.halfChartValueL p k j w₀)) :=
    ((A.halfChartValueL p k j).continuous.tendsto w₀).comp hlim
  -- Almost everywhere convergence of the chart-`i'` data along a subsequence, then of the
  -- chart-`i` data along a further subsequence.
  obtain ⟨ns, hns, hae'⟩ := (tendstoInMeasure_of_tendsto_Lp (hc i')).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((hc i).comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hrel : ∀ᵐ z ∂volume.restrict (A.halfOverlap i i'), ∀ m,
      A.halfChartValueL p k i' (w m) z = (A.triv i).coordChangeL ℝ (A.triv i')
        ((A.chart i').symm (closedUpperHalfPlaneModel.symm z))
        (A.halfChartValueL p k i (w m) (A.halfTransition i i' z)) :=
    ae_all_iff.2 fun m ↦ by simpa only [mem_ofPred_eq, halfCompatible_iff] using hw m
  simp only [mem_ofPred_eq, halfCompatible_iff]
  filter_upwards [hrel, ae_restrict_of_ae_restrict_of_subset
    (A.halfOverlap_subset_halfImage i i') hae',
    A.ae_restrict_halfOverlap_halfTransition (i' := i') hae] with z hz h' h
  refine tendsto_nhds_unique (h'.comp hms.tendsto_atTop) ?_
  refine ((((A.triv i).coordChangeL ℝ (A.triv i')
    ((A.chart i').symm (closedUpperHalfPlaneModel.symm z))).continuous.tendsto _).comp h).congr
      fun m ↦ ?_
  exact (hz (ns (ms m))).symm

end FiniteBundleAtlas

/-- The chartwise Sobolev components of sections form a closed subspace of the product of scalar
Sobolev spaces. -/
theorem isClosed_borderedSobolevSections [IsManifold closedUpperHalfPlaneModel 1 M] :
    IsClosed (borderedSobolevSections A p k : Set (BorderedSobolevData A p k)) := by
  have : (borderedSobolevSections A p k : Set (BorderedSobolevData A p k)) =
      ⋂ i, ⋂ i', {w | A.HalfCompatible p k w i i'} := by
    ext w
    simp only [SetLike.mem_coe, mem_borderedSobolevSections_iff_forall_halfCompatible, mem_iInter,
      mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun i' ↦ isClosed_setOf_halfCompatible i i'

/-- The Sobolev space `W^{k,p}(V)` of sections of `V` over a base with boundary, with respect to
the finite bundle atlas `A`: the tuples of chartwise Sobolev components of sections, with the
maximum of the component norms. -/
abbrev BorderedSobolevSection : Type :=
  borderedSobolevSections A p k

/-- **Completeness.** The Sobolev space of sections of a vector bundle over a base with boundary
is a Banach space. -/
instance BorderedSobolevSection.instCompleteSpace [IsManifold closedUpperHalfPlaneModel 1 M] :
    CompleteSpace (BorderedSobolevSection A p k) :=
  (isClosed_borderedSobolevSections A p k).completeSpace_coe

namespace BorderedSobolevSection

/-- An element of `W^{k,p}(V)` consists of the chartwise components of a section. -/
theorem exists_section (w : BorderedSobolevSection A p k) :
    ∃ s : ∀ x, V x, ∀ i,
      A.halfChartValueL p k i w =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s :=
  w.2

/-- Two elements of `W^{k,p}(V)` are equal when their components have equal values. -/
theorem ext {w w' : BorderedSobolevSection A p k}
    (h : ∀ i j, Wkp.value k ((w : BorderedSobolevData A p k) i j) =
      Wkp.value k ((w' : BorderedSobolevData A p k) i j)) : w = w' :=
  Subtype.ext <| funext fun i ↦ funext fun j ↦ Wkp.ext k (h i j)

/-- The continuous inclusion `W^{k+1,p}(V) → W^{k,p}(V)`, forgetting the highest derivative of
every component. -/
def lowerOrderL : BorderedSobolevSection A p (k + 1) →L[ℝ] BorderedSobolevSection A p k :=
  ((ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.pi fun j ↦ (Wkp.lowerOrderL k).comp
    ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (finrank ℝ F) ↦ Wkp volume (A.halfImage i) p (k + 1)) j).comp
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun i : Fin A.n ↦ ∀ _ : Fin (finrank ℝ F), Wkp volume (A.halfImage i) p (k + 1))
          i))).comp
    (borderedSobolevSections A p (k + 1)).subtypeL).codRestrict (borderedSobolevSections A p k)
      fun w ↦ by
        obtain ⟨s, hs⟩ := w.2
        refine ⟨s, fun i ↦ ?_⟩
        convert hs i using 2
        rw [← A.halfChartValueL_lowerOrderL p k i w]
        rfl

@[simp]
theorem lowerOrderL_apply (w : BorderedSobolevSection A p (k + 1)) (i : Fin A.n)
    (j : Fin (finrank ℝ F)) :
    (lowerOrderL A p k w : BorderedSobolevData A p k) i j =
      Wkp.lowerOrder k ((w : BorderedSobolevData A p (k + 1)) i j) := by
  rw [← Wkp.lowerOrderL_apply]
  rfl

end BorderedSobolevSection

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

/-- The tuple of chartwise `W^{k,p}` components of a `Cᵏ` section. -/
private def toBorderedSobolevData (s : Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯) :
    BorderedSobolevData A p k :=
  fun i j ↦ (exists_value_ae_eq_halfCoord A p k s i j).choose

private theorem value_toBorderedSobolevData_ae (s : Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯)
    (i : Fin A.n) (j : Fin (finrank ℝ F)) :
    (Wkp.value k (toBorderedSobolevData A p k s i j) : ℂ → ℝ)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        fun z ↦ (finBasis ℝ F).coord j (A.halfCoord i s z) :=
  (exists_value_ae_eq_halfCoord A p k s i j).choose_spec

private theorem halfChartValueL_toBorderedSobolevData_ae
    (s : Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯) (i : Fin A.n) :
    A.halfChartValueL p k i (toBorderedSobolevData A p k s)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s := by
  filter_upwards [A.halfChartValueL_apply_ae p k i (toBorderedSobolevData A p k s),
    ae_all_iff.2 (value_toBorderedSobolevData_ae A p k s i)] with y hy hj
  rw [hy]
  simp_rw [hj, Basis.coord_apply]
  exact (finBasis ℝ F).sum_repr _

/-- **`Cᵏ` sections are Sobolev sections.** The linear map sending a `Cᵏ` section `s` of `V` to the
element of `W^{k,p}(V)` whose components in chart `i` are the components of `A.halfCoord i s` in
the basis `Module.finBasis ℝ F`. -/
def ofContMDiffSection :
    Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯ →ₗ[ℝ] BorderedSobolevSection A p k where
  toFun s := ⟨toBorderedSobolevData A p k s, (mem_borderedSobolevSections_iff A p k).2
    ⟨s, halfChartValueL_toBorderedSobolevData_ae A p k s⟩⟩
  map_add' s t := ext A p k fun i j ↦ Lp.ext <| by
    filter_upwards [value_toBorderedSobolevData_ae A p k (s + t) i j,
      value_toBorderedSobolevData_ae A p k s i j, value_toBorderedSobolevData_ae A p k t i j,
      Wkp.value_add k (toBorderedSobolevData A p k s i j) (toBorderedSobolevData A p k t i j) ▸
        Lp.coeFn_add _ _, ae_restrict_mem (A.halfImage i).isOpen.measurableSet]
      with y h h₁ h₂ hadd hy
    simp only [Submodule.coe_add, Pi.add_apply] at hadd ⊢
    rw [h, hadd, h₁, h₂, ContMDiffSection.coe_add, A.halfCoord_add i s t hy, map_add]
  map_smul' c s := ext A p k fun i j ↦ Lp.ext <| by
    filter_upwards [value_toBorderedSobolevData_ae A p k (c • s) i j,
      value_toBorderedSobolevData_ae A p k s i j,
      Wkp.value_smul k c (toBorderedSobolevData A p k s i j) ▸ Lp.coeFn_smul _ _,
      ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with y h h₁ hsmul hy
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply] at hsmul ⊢
    rw [h, hsmul, h₁, ContMDiffSection.coe_smul, A.halfCoord_smul i c s hy, map_smul,
      smul_eq_mul]

/-- The components in chart `i` of the Sobolev section of a `Cᵏ` section `s` are the components
of `A.halfCoord i s` in the basis `Module.finBasis ℝ F`, almost everywhere on the interior of the
image of the chart. -/
theorem value_ofContMDiffSection_ae (s : Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯) (i : Fin A.n)
    (j : Fin (finrank ℝ F)) :
    (Wkp.value k ((ofContMDiffSection A p k s : BorderedSobolevData A p k) i j) : ℂ → ℝ)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        fun z ↦ (finBasis ℝ F).coord j (A.halfCoord i s z) :=
  value_toBorderedSobolevData_ae A p k s i j

/-- The chart data in chart `i` of the Sobolev section of a `Cᵏ` section `s` are the coordinates
`A.halfCoord i s`, almost everywhere on the interior of the image of the chart. -/
theorem halfChartValueL_ofContMDiffSection_ae (s : Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯)
    (i : Fin A.n) :
    A.halfChartValueL p k i (ofContMDiffSection A p k s)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s :=
  halfChartValueL_toBorderedSobolevData_ae A p k s i

/-- **Norm bound.** The norm of the Sobolev section of a `Cᵏ` section `s` is at most the sum, over
all charts `i` and basis vectors `j`, of the `Lᵖ` norms on `A.halfImage i` of the classical
derivatives of orders `0` through `k` of the components of `A.halfCoord i s`. -/
theorem norm_ofContMDiffSection_le (s : Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯) :
    ‖ofContMDiffSection A p k s‖ ≤ ∑ i, ∑ j, ∑ l ∈ Finset.range (k + 1),
      lpNorm (iteratedFDeriv ℝ l fun z ↦ (finBasis ℝ F).coord j (A.halfCoord i s z)) p
        (volume.restrict (A.halfImage i : Set ℂ)) := by
  have hcomp (i : Fin A.n) (j : Fin (finrank ℝ F)) :
      ‖(ofContMDiffSection A p k s : BorderedSobolevData A p k) i j‖ ≤
        ∑ l ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ l
          fun z ↦ (finBasis ℝ F).coord j (A.halfCoord i s z)) p
            (volume.restrict (A.halfImage i : Set ℂ)) :=
    Wkp.norm_le_sum_lpNorm_iteratedFDeriv_of_contDiffOn k _
      ((contDiffOn_coord_halfCoord A k s i j).mono (A.halfImage_subset_halfChartSet i))
      (value_ofContMDiffSection_ae A p k s i j)
  have hnonneg (i : Fin A.n) (j : Fin (finrank ℝ F)) :
      0 ≤ ∑ l ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv ℝ l
        fun z ↦ (finBasis ℝ F).coord j (A.halfCoord i s z)) p
          (volume.restrict (A.halfImage i : Set ℂ)) :=
    Finset.sum_nonneg fun _ _ ↦ lpNorm_nonneg
  -- The norm of a tuple is the maximum of the component norms, bounded by their sum.
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦ hnonneg i j)).2 fun i ↦ ?_
  refine ((pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ ↦ hnonneg i j)).2 fun j ↦
    (hcomp i j).trans (Finset.single_le_sum (fun j _ ↦ hnonneg i j) (Finset.mem_univ j))).trans
      (Finset.single_le_sum (f := fun i ↦ ∑ j, ∑ l ∈ Finset.range (k + 1), lpNorm (iteratedFDeriv
        ℝ l fun z ↦ (finBasis ℝ F).coord j (A.halfCoord i s z)) p
          (volume.restrict (A.halfImage i : Set ℂ)))
        (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnonneg i j) (Finset.mem_univ i))

/-- **Injectivity.** A `Cᵏ` section whose Sobolev section vanishes is zero: its chart coordinates
vanish almost everywhere on the interiors of the chart images, hence everywhere there by
continuity, and hence also on the real axis, whose points are limits of interior points. -/
theorem ofContMDiffSection_injective : Function.Injective (ofContMDiffSection A p k) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs ↦ ContMDiffSection.ext fun x ↦ ?_
  obtain ⟨i, hx⟩ := A.exists_mem_dom x
  have hcont : ContinuousOn (A.halfCoord i s) (A.halfChartSet i) :=
    (A.contDiffOn_halfCoord s.contMDiff i).continuousOn
  -- The chart data of the zero tuple vanish, so `A.halfCoord i s` vanishes almost everywhere.
  have h0 : A.halfChartValueL p k i
      (ofContMDiffSection A p k s : BorderedSobolevData A p k) = 0 := by
    rw [hs, ZeroMemClass.coe_zero, map_zero]
  have hz := Lp.coeFn_zero F p (volume.restrict (A.halfImage i : Set ℂ))
  rw [← h0] at hz
  have hae : A.halfCoord i s =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] fun _ ↦ 0 :=
    (halfChartValueL_ofContMDiffSection_ae A p k s i).symm.trans hz
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

omit [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- The components of the chart data of a tuple of Sobolev functions are the values of its
entries: if the chart data in chart `i` agree with `A.halfCoord i s`, then the `j`th component of
`A.halfCoord i s` in the basis `Module.finBasis ℝ F` is the value of the entry `w i j`, almost
everywhere on `A.halfImage i`. -/
private theorem value_ae_eq_repr_halfCoord {w : BorderedSobolevData A p k} {s : ∀ x, V x}
    {i : Fin A.n}
    (hs : A.halfChartValueL p k i w =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (j : Fin (finrank ℝ F)) :
    (Wkp.value k (w i j) : ℂ → ℝ) =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
      fun z ↦ (finBasis ℝ F).repr (A.halfCoord i s z) j := by
  filter_upwards [A.halfChartValueL_apply_ae p k i w, hs] with y hy hy'
  rw [← hy', hy, (finBasis ℝ F).repr_sum_self]

/-- **Localization up to the boundary.** If the chart data of an element `w` of `W^{k,p}(V)` are
the coordinates of the section `s`, then in every chart `i` the chart expression `A.halfCoord i s`
lies in the local Sobolev class `MemWkpLoc p (A.halfClosedImage i) k` on the image of the chart in
the closed upper half-plane, with `Lᵖ` bounds on compact sets reaching the real axis. -/
theorem memWkpLoc_halfCoord (w : BorderedSobolevSection A p k) {s : ∀ x, V x}
    (hs : ∀ i, A.halfChartValueL p k i w =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
      A.halfCoord i s)
    (i : Fin A.n) : MemWkpLoc p (A.halfClosedImage i) k (A.halfCoord i s) :=
  (finBasis ℝ F).memWkpLoc_iff.2 fun j ↦
    (memWkpLoc_value_of_ae_le (A.interior_halfClosedImage i) (A.halfClosedImage_ae_le_halfImage i)
      k _).congr_ae (ae_mono (Measure.restrict_mono_ae (A.halfClosedImage_ae_le_halfImage i))
        (value_ae_eq_repr_halfCoord (hs i) j))

/-- **Localization up to the boundary.** Every element of `W^{k,p}(V)` consists of the components
of a section whose chart expression in every chart `i` lies in the local Sobolev class
`MemWkpLoc p (A.halfClosedImage i) k`. -/
theorem exists_section_memWkpLoc (w : BorderedSobolevSection A p k) :
    ∃ s : ∀ x, V x, (∀ i, A.halfChartValueL p k i w =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
      A.halfCoord i s) ∧ ∀ i, MemWkpLoc p (A.halfClosedImage i) k (A.halfCoord i s) := by
  obtain ⟨s, hs⟩ := exists_section A p k w
  exact ⟨s, hs, memWkpLoc_halfCoord w hs⟩

end BorderedSobolevSection

end Localization

end TauCeti
