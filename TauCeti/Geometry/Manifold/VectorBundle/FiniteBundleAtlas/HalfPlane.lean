/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Geometry.Manifold.Complex.ClosedUpperHalfPlane
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Complex.EvenReflection
import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Finite bundle atlases over the closed upper half-plane

Let `M` be a manifold modelled on the closed upper half-plane `ClosedUpperHalfPlane`, for instance
a surface with boundary, and let `A : TauCeti.FiniteBundleAtlas ClosedUpperHalfPlane M F V` be a
finite bundle atlas of a fibre bundle `V → M`. This file reads the charts of `A` in `ℂ`.

The image of chart `i` is a relatively open subset of the closed upper half-plane; in `ℂ` it is
`A.halfClosedImage i = Ω ∩ {0 ≤ im}` for an open set `Ω`, and its interior is the open set
`A.halfImage i = Ω ∩ {0 < im}` (`TauCeti.FiniteBundleAtlas.interior_halfClosedImage`). The two
differ by a subset of the real axis, a Lebesgue null set
(`TauCeti.FiniteBundleAtlas.halfClosedImage_ae_le_halfImage`), and every point of the image is a
limit of interior points (`TauCeti.FiniteBundleAtlas.halfClosedImage_subset_closure_halfImage`).

Chart transitions `A.halfTransition i i'` carry interior points to interior points
(`TauCeti.ClosedUpperHalfPlane.im_pos_iff_of_mem_contDiffGroupoid`), and are differentiable on the
interiors `A.halfOverlap i i'` of the overlaps for a `C¹` manifold. In chart `i` a section `s` is
read as the function `A.halfCoord i s` on `ℂ`; for a `Cᵏ` section of a `Cᵏ` vector bundle it is
`Cᵏ` up to the real axis (`TauCeti.FiniteBundleAtlas.contDiffOn_halfCoord`).

## Main definitions

* `TauCeti.FiniteBundleAtlas.halfImage`, `TauCeti.FiniteBundleAtlas.halfClosedImage`: the
  interior in `ℂ` of the image of a chart, and the image itself.
* `TauCeti.FiniteBundleAtlas.halfOverlap`, `TauCeti.FiniteBundleAtlas.halfTransition`: the
  interiors of the overlaps and the chart transitions, in `ℂ`.
* `TauCeti.FiniteBundleAtlas.halfCoord`: a section read in a chart, as a function on `ℂ`.

## Main results

* `TauCeti.FiniteBundleAtlas.halfTransition_mem_halfOverlap`,
  `TauCeti.FiniteBundleAtlas.differentiableOn_halfTransition`: chart transitions keep interior
  points interior and are differentiable there.
* `TauCeti.FiniteBundleAtlas.halfCoord_eq_coordChange`: coordinates in two charts differ by the
  coordinate change of the bundle.
* `TauCeti.FiniteBundleAtlas.contDiffOn_halfCoord`: the chart coordinates of a `Cᵏ` section are
  `Cᵏ` up to the boundary.
* `TauCeti.FiniteBundleAtlas.isCompact_closure_halfImage`,
  `TauCeti.FiniteBundleAtlas.closure_halfImage_subset_extChartAt_target`: the interior of a chart
  image has compact closure inside the target of the extended chart.
* `TauCeti.FiniteBundleAtlas.contDiffOn_comp_chart_symm_closedUpperHalfPlaneModel_symm`: the
  chart readings of a `Cⁿ` function are `Cⁿ` up to the boundary.
* `TauCeti.FiniteBundleAtlas.halfCoord_fun_smul`: chart readings of sections are linear over
  functions on `M`.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Set TopologicalSpace
open scoped Manifold Topology ContDiff

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

theorem mem_halfClosedImage {i : Fin A.n} {z : ℂ} :
    z ∈ A.halfClosedImage i ↔ closedUpperHalfPlaneModel.symm z ∈ A.image i ∧ 0 ≤ z.im :=
  Iff.rfl

theorem halfClosedImage_eq_image_val (i : Fin A.n) :
    A.halfClosedImage i = Subtype.val '' (A.image i : Set ClosedUpperHalfPlane) := by
  ext z
  refine ⟨fun ⟨hz, hz0⟩ ↦ ⟨_, hz, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz0⟩, ?_⟩
  rintro ⟨w, hw, rfl⟩
  exact ⟨by simpa using hw, w.2⟩

theorem halfImage_subset_halfClosedImage (i : Fin A.n) :
    (A.halfImage i : Set ℂ) ⊆ A.halfClosedImage i :=
  fun _ hz ↦ ⟨hz.1, (A.mem_halfImage.1 hz).2.le⟩

/-- The interior of the image of chart `i` in `ℂ` is `A.halfImage i`. -/
theorem interior_halfClosedImage (i : Fin A.n) :
    Opens.interior (A.halfClosedImage i) = A.halfImage i :=
  Opens.ext <| interior_inter_setOf_im_nonneg
    ((A.image i).isOpen.preimage closedUpperHalfPlaneModel.continuous_symm)

/-- The points of the image of chart `i` in `ℂ` that are not in its interior lie on the real
axis, so the image and its interior differ by a null set. -/
theorem halfClosedImage_ae_le_halfImage (i : Fin A.n) :
    A.halfClosedImage i ≤ᵐ[volume] (A.halfImage i : Set ℂ) :=
  (EventuallyEqSet.inter EventuallyEqSet.rfl (Complex.setOf_le_im_ae_eq 0)).subset

/-- Every point of the image of chart `i` in `ℂ`, including the points on the real axis, is a
limit of points of its interior. -/
theorem halfClosedImage_subset_closure_halfImage (i : Fin A.n) :
    A.halfClosedImage i ⊆ closure (A.halfImage i : Set ℂ) := by
  have hO := (A.image i).isOpen.preimage closedUpperHalfPlaneModel.continuous_symm
  have h := subset_closure_interior_setOfPred_le_im_inter hO
  rwa [inter_comm, interior_inter_setOf_im_nonneg hO] at h

/-- The overlap of the domains of charts `i` and `i'`, read in chart `i'`, at points of positive
imaginary part. -/
def halfOverlap (i i' : Fin A.n) : Set ℂ :=
  closedUpperHalfPlaneModel.symm ⁻¹' A.overlap i i' ∩ {z : ℂ | 0 < z.im}

theorem mem_halfOverlap {i i' : Fin A.n} {z : ℂ} :
    z ∈ A.halfOverlap i i' ↔ closedUpperHalfPlaneModel.symm z ∈ A.overlap i i' ∧ 0 < z.im :=
  Iff.rfl

theorem isOpen_halfOverlap (i i' : Fin A.n) : IsOpen (A.halfOverlap i i') :=
  ((A.isOpen_overlap i i').preimage closedUpperHalfPlaneModel.continuous_symm).inter
    (isOpen_lt continuous_const Complex.continuous_im)

theorem halfOverlap_subset_halfImage (i i' : Fin A.n) :
    A.halfOverlap i i' ⊆ A.halfImage i' :=
  fun _ hz ↦ ⟨A.overlap_subset_image i i' hz.1, hz.2⟩

/-- The chart transition from chart `i'` to chart `i`, as a function on `ℂ`. -/
def halfTransition (i i' : Fin A.n) (z : ℂ) : ℂ :=
  A.transition i i' (closedUpperHalfPlaneModel.symm z)

theorem halfTransition_def (i i' : Fin A.n) (z : ℂ) :
    A.halfTransition i i' z = A.transition i i' (closedUpperHalfPlaneModel.symm z) :=
  (rfl)

theorem symm_halfTransition (i i' : Fin A.n) (z : ℂ) :
    closedUpperHalfPlaneModel.symm (A.halfTransition i i' z) =
      A.transition i i' (closedUpperHalfPlaneModel.symm z) :=
  closedUpperHalfPlaneModel_symm_coe _

/-- A point of the closed upper half-plane, read in `ℂ` and transported by a chart transition,
is the chart transition of the point. -/
theorem halfTransition_coe_chart {i i' : Fin A.n} {x : M} (hx : x ∈ A.dom i') :
    A.halfTransition i i' (A.chart i' x : ℂ) = A.chart i x := by
  rw [halfTransition, closedUpperHalfPlaneModel_symm_coe, A.transition_chart hx]

/-- Chart transitions are continuous on the overlaps, read in `ℂ`, including their points on the
real axis. -/
theorem continuousOn_halfTransition (i i' : Fin A.n) :
    ContinuousOn (A.halfTransition i i') (closedUpperHalfPlaneModel.symm ⁻¹' A.overlap i i') := by
  have h : ContinuousOn (fun y ↦ A.chart i ((A.chart i').symm y)) (A.overlap i i') :=
    (A.chart i).continuousOn.comp ((A.continuousOn_chart_symm i').mono
      (A.overlap_subset_image i i')) fun y hy ↦ by
        obtain ⟨x, hx, rfl⟩ := A.mem_overlap.1 hy
        rw [(A.chart i').left_inv (A.dom_subset_chart_source i' hx.2)]
        exact A.dom_subset_chart_source i hx.1
  refine (continuous_subtype_val.comp_continuousOn (h.comp
    closedUpperHalfPlaneModel.continuous_symm.continuousOn fun _ hz ↦ hz)).congr fun z hz ↦ ?_
  obtain ⟨x, hx, hxz⟩ := A.mem_overlap.1 hz
  simp only [Function.comp_apply, halfTransition, ← hxz, A.transition_chart hx.2,
    (A.chart i').left_inv (A.dom_subset_chart_source i' hx.2)]

/-- A section read in chart `i`, as a function on `ℂ`. -/
def halfCoord (i : Fin A.n) (s : ∀ x, V x) (z : ℂ) : F :=
  A.coord i s (closedUpperHalfPlaneModel.symm z)

theorem halfCoord_def (i : Fin A.n) (s : ∀ x, V x) (z : ℂ) :
    A.halfCoord i s z = A.coord i s (closedUpperHalfPlaneModel.symm z) :=
  (rfl)

theorem halfCoord_coe_chart {i : Fin A.n} (s : ∀ x, V x) {x : M} (hx : x ∈ A.dom i) :
    A.halfCoord i s (A.chart i x : ℂ) = (A.triv i ⟨x, s x⟩).2 := by
  rw [halfCoord, closedUpperHalfPlaneModel_symm_coe, A.coord_chart s hx]

/-- The chart expression in chart `i` of a continuous section is continuous on the image of the
chart in `ℂ`, including its points on the real axis. -/
theorem continuousOn_halfCoord {s : ∀ x, V x} (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (i : Fin A.n) : ContinuousOn (A.halfCoord i s) (A.halfClosedImage i) :=
  ((A.continuousOn_coord hs i).comp closedUpperHalfPlaneModel.continuous_symm.continuousOn
    fun _ hz ↦ (A.mem_halfClosedImage.1 hz).1).congr fun z _ ↦ A.halfCoord_def i s z

/-- The extended chart `i` sends a point to its image under the manifold chart, read in `ℂ`. -/
theorem extChartAt_center_apply (i : Fin A.n) (x : M) :
    extChartAt closedUpperHalfPlaneModel (A.center i) x = (A.chart i x : ℂ) := by
  rw [extChartAt_coe, Function.comp_apply, closedUpperHalfPlaneModel_apply]

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
  intro z hz
  obtain ⟨hz, hz0⟩ := A.mem_halfImage.1 hz
  obtain ⟨x, hx, hxz⟩ := A.mem_image.1 hz
  refine ⟨x, subset_closure hx, ?_⟩
  rw [extChartAt_center_apply, hxz, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz0.le]

theorem halfImage_subset_halfChartSet (i : Fin A.n) :
    (A.halfImage i : Set ℂ) ⊆ A.halfChartSet i :=
  (A.halfImage_subset_extChartAt_image_closure_dom i).trans
    (A.extChartAt_image_closure_dom_subset_halfChartSet i)

/-- The closure of the interior of the image of chart `i` in `ℂ` lies in the compact image of the
closure of the chart domain. -/
private theorem closure_halfImage_subset_extChartAt_image_closure_dom (i : Fin A.n) :
    closure (A.halfImage i : Set ℂ) ⊆
      extChartAt closedUpperHalfPlaneModel (A.center i) '' closure (A.dom i) :=
  closure_minimal (A.halfImage_subset_extChartAt_image_closure_dom i)
    (A.isCompact_extChartAt_image_closure_dom i).isClosed

/-- The interior of the image of chart `i` in `ℂ` has compact closure. -/
theorem isCompact_closure_halfImage (i : Fin A.n) : IsCompact (closure (A.halfImage i : Set ℂ)) :=
  (A.isCompact_extChartAt_image_closure_dom i).of_isClosed_subset isClosed_closure
    (A.closure_halfImage_subset_extChartAt_image_closure_dom i)

/-- The closure of the interior of the image of chart `i` in `ℂ`, including its points on the real
axis, lies in the target of the extended chart `i`, a relatively open subset of the closed upper
half-plane. -/
theorem closure_halfImage_subset_extChartAt_target (i : Fin A.n) :
    closure (A.halfImage i : Set ℂ) ⊆ (extChartAt closedUpperHalfPlaneModel (A.center i)).target :=
  (A.closure_halfImage_subset_extChartAt_image_closure_dom i).trans <| by
    rintro _ ⟨x, hx, rfl⟩
    exact (extChartAt closedUpperHalfPlaneModel (A.center i)).map_source (by
      rw [extChartAt_source]; exact A.closure_dom_subset_source i hx)

/-- **The chart readings of a `Cⁿ` function are `Cⁿ` up to the boundary**, on the target of the
extended chart, a relatively open subset of the closed upper half-plane. -/
theorem contDiffOn_comp_chart_symm_closedUpperHalfPlaneModel_symm {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : WithTop ℕ∞} [IsManifold closedUpperHalfPlaneModel n M] {φ : M → G}
    (hφ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ, G) n φ) (i : Fin A.n) :
    ContDiffOn ℝ n (fun z ↦ φ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)))
      (extChartAt closedUpperHalfPlaneModel (A.center i)).target := by
  rw [← contMDiffOn_iff_contDiffOn]
  refine (hφ.contMDiffOn.comp (t := univ) (contMDiffOn_extChartAt_symm (A.center i))
    fun _ _ ↦ mem_univ _).congr fun z _ ↦ ?_
  rw [Function.comp_apply, extChartAt_coe_symm, Function.comp_apply]

variable [IsManifold closedUpperHalfPlaneModel 1 M]

/-- Chart transitions carry interior points of the overlap to interior points. -/
theorem halfTransition_mem_halfOverlap {i i' : Fin A.n} {z : ℂ} (hz : z ∈ A.halfOverlap i i') :
    A.halfTransition i i' z ∈ A.halfOverlap i' i := by
  obtain ⟨hz, hz0⟩ := A.mem_halfOverlap.1 hz
  obtain ⟨x, hx, hxz⟩ := A.mem_overlap.1 hz
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
    coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (A.mem_halfOverlap.1 hz).2.le]

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
  intro z hz
  obtain ⟨hz, hz0⟩ := A.mem_halfOverlap.1 hz
  obtain ⟨x, hx, hxz⟩ := A.mem_overlap.1 hz
  have hx' : x ∈ (A.chart i').source := A.dom_subset_chart_source i' hx.2
  have hzr : z ∈ range closedUpperHalfPlaneModel := by
    rw [range_closedUpperHalfPlaneModel]; exact hz0.le
  simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage,
    extChartAt_target, extChartAt_source, extChartAt_coe_symm, Function.comp_apply]
  refine ⟨⟨?_, hzr⟩, ?_⟩
  · rw [← hxz]; exact (A.chart i').map_source hx'
  · rw [← hxz, (A.chart i').left_inv hx']; exact A.dom_subset_chart_source i hx.1

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

/-- On the image of chart `i`, including its points on the real axis, the chart reading of
`x ↦ φ x • s x` is the chart reading of `φ` times that of `s`. -/
theorem halfCoord_fun_smul (i : Fin A.n) (φ : M → ℝ) (s : ∀ x, V x) {z : ℂ}
    (hz : closedUpperHalfPlaneModel.symm z ∈ A.image i) :
    A.halfCoord i (fun x ↦ φ x • s x) z =
      φ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)) • A.halfCoord i s z := by
  rw [halfCoord_def, halfCoord_def]
  exact A.coord_fun_smul i φ s hz

end FiniteBundleAtlas

end Linear

end TauCeti
