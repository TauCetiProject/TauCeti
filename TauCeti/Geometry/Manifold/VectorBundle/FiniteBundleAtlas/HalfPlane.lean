/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import TauCeti.Analysis.Complex.ReImTopology
public import TauCeti.Geometry.Manifold.Complex.ClosedUpperHalfPlane
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.MeasureTheory.Function.Jacobian
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
interiors `A.halfOverlap i i'` of the overlaps for a `C¹` manifold. The same holds for transitions
between the charts of two atlases `A` and `A'`: they keep interior points interior, are
differentiable there, and pull back null sets, and the readings of a section in the two atlases
differ by the coordinate changes of the bundle; this is the input to the change of atlas for
Sobolev sections over bases with boundary. In chart `i` a section `s` is
read as the function `A.halfCoord i s` on `ℂ`; for a `Cᵏ` section of a `Cᵏ` vector bundle it is
`Cᵏ` up to the real axis (`TauCeti.FiniteBundleAtlas.contDiffOn_halfCoord`).

## Main definitions

* `TauCeti.FiniteBundleAtlas.halfImage`, `TauCeti.FiniteBundleAtlas.halfClosedImage`: the
  interior in `ℂ` of the image of a chart, and the image itself.
* `TauCeti.FiniteBundleAtlas.halfOpen`: an open subset of `ℂ` whose trace on the closed upper
  half-plane is the image of a chart.
* `TauCeti.FiniteBundleAtlas.halfOverlap`, `TauCeti.FiniteBundleAtlas.halfTransition`: the
  interiors of the overlaps and the chart transitions, in `ℂ`.
* `TauCeti.FiniteBundleAtlas.halfCoord`: a section read in a chart, as a function on `ℂ`.

## Main results

* `TauCeti.FiniteBundleAtlas.coe_chart_mem_halfImage`,
  `TauCeti.FiniteBundleAtlas.differentiableOn_coe_chart_chart_symm`: transitions between the charts
  of two atlases keep interior points interior and are differentiable there.
* `TauCeti.FiniteBundleAtlas.ae_restrict_halfImage_chart_symm`: transitions between two atlases
  pull back null sets.
* `TauCeti.FiniteBundleAtlas.halfCoord_eq_coordChangeL_halfCoord`: readings of a section in charts
  of two atlases differ by the coordinate change of the bundle.
* `TauCeti.FiniteBundleAtlas.halfTransition_mem_halfOverlap`,
  `TauCeti.FiniteBundleAtlas.differentiableOn_halfTransition`: chart transitions keep interior
  points interior and are differentiable there.
* `TauCeti.FiniteBundleAtlas.halfCoord_eq_coordChange`: coordinates in two charts differ by the
  coordinate change of the bundle.
* `TauCeti.FiniteBundleAtlas.exists_continuous_halfCoord_eqOn`: functions continuous on the chart
  images and related by the coordinate changes on the interiors of the overlaps are the chart
  expressions of a continuous section.
* `TauCeti.FiniteBundleAtlas.eqOn_halfClosedImage_of_ae_eq`: functions continuous on a chart
  image that agree almost everywhere on its interior agree on the whole image.
* `TauCeti.FiniteBundleAtlas.eq_of_continuous_of_halfCoord_ae_eq`: continuous sections are
  determined by their chart expressions almost everywhere.
* `TauCeti.FiniteBundleAtlas.contDiffOn_halfCoord`: the chart coordinates of a `Cᵏ` section are
  `Cᵏ` up to the boundary.
* `TauCeti.FiniteBundleAtlas.isCompact_closure_halfImage`,
  `TauCeti.FiniteBundleAtlas.closure_halfImage_subset_extChartAt_target`: the interior of a chart
  image has compact closure inside the target of the extended chart.
* `TauCeti.FiniteBundleAtlas.continuousOn_halfCoord_closure_halfImage`: the chart expression of a
  continuous section is continuous on that closure.
* `TauCeti.FiniteBundleAtlas.contDiffOn_comp_chart_symm_closedUpperHalfPlaneModel_symm`: the
  chart readings of a `Cⁿ` function are `Cⁿ` up to the boundary.
* `TauCeti.FiniteBundleAtlas.halfCoord_fun_smul`: chart readings of sections are linear over
  functions on `M`.
* `TauCeti.FiniteBundleAtlas.contMDiff_smul_chartSection_coe`,
  `TauCeti.FiniteBundleAtlas.halfCoord_smul_chartSection_coe`: the section equal in one chart to
  `ψ • G`, for a cutoff `ψ` and `G` smooth up to the real axis, is smooth, with that reading.
* `TauCeti.FiniteBundleAtlas.halfCoord_focus`, `TauCeti.FiniteBundleAtlas.halfCoord_focus_eq_zero`:
  readings in `TauCeti.FiniteBundleAtlas.focus`.
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

@[simp]
theorem coe_mem_halfClosedImage {i : Fin A.n} {y : ClosedUpperHalfPlane} :
    (y : ℂ) ∈ A.halfClosedImage i ↔ y ∈ A.image i := by
  rw [mem_halfClosedImage, closedUpperHalfPlaneModel_symm_coe]
  exact and_iff_left y.property

/-- The open subset of `ℂ` whose trace on the closed upper half-plane is the image of chart `i`. -/
def halfOpen (i : Fin A.n) : Opens ℂ :=
  ⟨closedUpperHalfPlaneModel.symm ⁻¹' (A.image i : Set ClosedUpperHalfPlane),
    (A.image i).isOpen.preimage closedUpperHalfPlaneModel.continuous_symm⟩

theorem mem_halfOpen {i : Fin A.n} {z : ℂ} :
    z ∈ A.halfOpen i ↔ closedUpperHalfPlaneModel.symm z ∈ A.image i :=
  Iff.rfl

/-- The interior `A.halfImage i` of the image of chart `i` in `ℂ` is the upper half of the open
set `A.halfOpen i`. -/
theorem upperHalf_halfOpen (i : Fin A.n) : (A.halfOpen i).upperHalf = A.halfImage i :=
  Opens.ext <| Set.ext fun _ ↦ by
    rw [SetLike.mem_coe, SetLike.mem_coe, Opens.mem_upperHalf, mem_halfImage, mem_halfOpen]

/-- The image of chart `i` in `ℂ` is the trace of the open set `A.halfOpen i` on the closed upper
half-plane. -/
theorem halfClosedImage_eq_inter (i : Fin A.n) :
    A.halfClosedImage i = (A.halfOpen i : Set ℂ) ∩ {z : ℂ | 0 ≤ z.im} :=
  Set.ext fun _ ↦ A.mem_halfClosedImage

theorem halfClosedImage_eq_image_val (i : Fin A.n) :
    A.halfClosedImage i = Subtype.val '' (A.image i : Set ClosedUpperHalfPlane) := by
  ext z
  refine ⟨fun ⟨hz, hz0⟩ ↦ ⟨_, hz, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz0⟩, ?_⟩
  rintro ⟨w, hw, rfl⟩
  exact ⟨by simpa using hw, w.property⟩

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
    A.halfClosedImage i ≤ᵐ[volume] (A.halfImage i : Set ℂ) := by
  rw [← A.interior_halfClosedImage]
  exact (inter_setOf_im_nonneg_ae_eq_interior
    ⟨_, (A.image i).isOpen.preimage closedUpperHalfPlaneModel.continuous_symm⟩).subset

/-- Every point of the image of chart `i` in `ℂ`, including the points on the real axis, is a
limit of points of its interior. -/
theorem halfClosedImage_subset_closure_halfImage (i : Fin A.n) :
    A.halfClosedImage i ⊆ closure (A.halfImage i : Set ℂ) := by
  have hO := (A.image i).isOpen.preimage closedUpperHalfPlaneModel.continuous_symm
  have h := subset_closure_interior_inter_setOf_im_nonneg hO
  rwa [interior_inter_setOf_im_nonneg hO] at h

/-- Two functions continuous on the image of chart `i` in `ℂ` that agree almost everywhere on its
interior, for a measure charging nonempty open sets, agree on the whole image, including its points
on the real axis. -/
theorem eqOn_halfClosedImage_of_ae_eq {X : Type*} [TopologicalSpace X] [T2Space X]
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] {i : Fin A.n} {f g : ℂ → X}
    (h : f =ᵐ[μ.restrict (A.halfImage i : Set ℂ)] g) (hf : ContinuousOn f (A.halfClosedImage i))
    (hg : ContinuousOn g (A.halfClosedImage i)) : EqOn f g (A.halfClosedImage i) := by
  have hsub := A.halfImage_subset_halfClosedImage i
  exact (Measure.eqOn_open_of_ae_eq h (A.halfImage i).isOpen (hf.mono hsub)
    (hg.mono hsub)).of_subset_closure hf hg hsub (A.halfClosedImage_subset_closure_halfImage i)

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

/-- Every point of the overlap of two charts read in `ℂ`, including its points on the real axis,
is a limit of points of the interior of the overlap. -/
theorem subset_closure_halfOverlap (i i' : Fin A.n) :
    closedUpperHalfPlaneModel.symm ⁻¹' A.overlap i i' ∩ {z : ℂ | 0 ≤ z.im} ⊆
      closure (A.halfOverlap i i') := by
  have hO := (A.isOpen_overlap i i').preimage closedUpperHalfPlaneModel.continuous_symm
  have h := subset_closure_interior_inter_setOf_im_nonneg hO
  rw [interior_inter_setOf_im_nonneg hO] at h
  exact h.trans (closure_mono fun _ hz ↦ A.mem_halfOverlap.2 hz)

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
    ContinuousOn (A.halfTransition i i') (closedUpperHalfPlaneModel.symm ⁻¹' A.overlap i i') :=
  continuous_subtypeVal.comp_continuousOn ((A.continuousOn_transition i i').comp
    closedUpperHalfPlaneModel.continuous_symm.continuousOn fun _ hz ↦ hz)

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

/-- **Continuous sections are determined by their chart expressions almost everywhere.** Two
continuous sections whose chart expressions in every chart `i` agree almost everywhere on the
interior `A.halfImage i` of the chart image, for a measure charging nonempty open sets, are
equal. -/
theorem eq_of_continuous_of_halfCoord_ae_eq [T2Space F] {μ : Measure ℂ} [μ.IsOpenPosMeasure]
    {s t : ∀ x, V x} (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (ht : Continuous fun x ↦ TotalSpace.mk' F x (t x))
    (h : ∀ i, A.halfCoord i s =ᵐ[μ.restrict (A.halfImage i : Set ℂ)] A.halfCoord i t) :
    s = t := by
  funext x
  obtain ⟨i, hx⟩ := A.exists_mem_dom x
  have hxz := A.eqOn_halfClosedImage_of_ae_eq (h i) (A.continuousOn_halfCoord hs i)
    (A.continuousOn_halfCoord ht i) (A.coe_mem_halfClosedImage.2 (A.mem_image.2 ⟨x, hx, rfl⟩))
  rw [halfCoord_def, halfCoord_def, closedUpperHalfPlaneModel_symm_coe] at hxz
  exact A.eq_of_coord_chart_eq hx hxz

/-- The readings of a section in the charts of `A.focus i hL hLi` are its readings in `A`. -/
@[simp]
theorem halfCoord_focus {i : Fin A.n} {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i)
    (j : Fin A.n) (s : ∀ x, V x) : (A.focus i hL hLi).halfCoord j s = A.halfCoord j s := by
  ext z
  rw [(A.focus i hL hLi).halfCoord_def j s z, A.halfCoord_def j s z, coord_focus]

/-- The interior of the image of a chart of `A.focus i hL hLi` lies in that of `A`. -/
theorem halfImage_focus_le {i : Fin A.n} {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i)
    (j : Fin A.n) : (A.focus i hL hLi).halfImage j ≤ A.halfImage j := by
  intro z hz
  obtain ⟨hz, hz0⟩ := (A.focus i hL hLi).mem_halfImage.1 hz
  obtain ⟨x, hx, hxz⟩ := (A.focus i hL hLi).mem_image.1 hz
  rw [chart_focus] at hxz
  exact A.mem_halfImage.2 ⟨A.mem_image.2 ⟨x, A.focus_dom_subset hL hLi j hx, hxz⟩, hz0⟩

/-- The readings of a section in the charts of `A.enlarge U hU hAU hUc hUs` are its readings in
`A`. -/
@[simp]
theorem halfCoord_enlarge {U : Fin A.n → Set M} {hU : ∀ j, IsOpen (U j)}
    {hAU : ∀ j, A.dom j ⊆ U j} {hUc : ∀ j, IsCompact (closure (U j))}
    {hUs : ∀ j, closure (U j) ⊆ (A.chart j).source ∩ (A.triv j).baseSet} (j : Fin A.n)
    (s : ∀ x, V x) : (A.enlarge U hU hAU hUc hUs).halfCoord j s = A.halfCoord j s := by
  ext z
  rw [(A.enlarge U hU hAU hUc hUs).halfCoord_def j s z, A.halfCoord_def j s z, coord_enlarge]

/-- The interiors of the chart images of `A` lie in those of `A.enlarge U hU hAU hUc hUs`. -/
theorem halfImage_le_halfImage_enlarge {U : Fin A.n → Set M} {hU : ∀ j, IsOpen (U j)}
    {hAU : ∀ j, A.dom j ⊆ U j} {hUc : ∀ j, IsCompact (closure (U j))}
    {hUs : ∀ j, closure (U j) ⊆ (A.chart j).source ∩ (A.triv j).baseSet} (j : Fin A.n) :
    A.halfImage j ≤ (A.enlarge U hU hAU hUc hUs).halfImage j := fun _ hz ↦
  (A.enlarge U hU hAU hUc hUs).mem_halfImage.2
    ⟨image_le_image_enlarge j (A.mem_halfImage.1 hz).1, (A.mem_halfImage.1 hz).2⟩

/-- The charts of `A`, as an atlas of another bundle, have the same interiors of chart images. -/
@[simp]
theorem halfImage_ofBaseSet {F' : Type*} [TopologicalSpace F'] {V' : M → Type*}
    [TopologicalSpace (TotalSpace F' V')] [∀ x, TopologicalSpace (V' x)] [FiberBundle F' V']
    {h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F' V' (A.center i)).baseSet} (i : Fin A.n) :
    (A.ofBaseSet h).halfImage i = A.halfImage i :=
  SetLike.ext fun _ ↦ (mem_halfImage (A := A.ofBaseSet h) (i := i)).trans <| by
    rw [image_ofBaseSet]
    exact (mem_halfImage (A := A)).symm

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

/-- A point of the closure of the interior of the image of chart `i` in `ℂ` comes from a point of
the closure of the chart domain. -/
theorem exists_mem_closure_dom_of_mem_closure_halfImage {i : Fin A.n} {z : ℂ}
    (hz : z ∈ closure (A.halfImage i : Set ℂ)) :
    ∃ x ∈ closure (A.dom i), closedUpperHalfPlaneModel.symm z = A.chart i x := by
  obtain ⟨x, hx, rfl⟩ := A.closure_halfImage_subset_extChartAt_image_closure_dom i hz
  exact ⟨x, hx, by rw [extChartAt_coe, Function.comp_apply, ModelWithCorners.left_inv]⟩

/-- A point of the closure of the interior of the image of chart `i` in `ℂ`, read back in `M`,
lies in the base set of the bundle chart `i`. -/
theorem chart_symm_mem_baseSet_of_mem_closure_halfImage {i : Fin A.n} {z : ℂ}
    (hz : z ∈ closure (A.halfImage i : Set ℂ)) :
    (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∈ (A.triv i).baseSet := by
  obtain ⟨x, hx, hxz⟩ := A.exists_mem_closure_dom_of_mem_closure_halfImage hz
  rw [hxz, (A.chart i).left_inv (A.closure_dom_subset_source i hx)]
  exact A.closure_dom_subset_baseSet i hx

/-- The chart expression in chart `i` of a continuous section is continuous on the closure of the
interior of the image of the chart in `ℂ`, which contains the points of the image on the real
axis and lies in the image of the closure of the chart domain. -/
theorem continuousOn_halfCoord_closure_halfImage {s : ∀ x, V x}
    (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x)) (i : Fin A.n) :
    ContinuousOn (A.halfCoord i s) (closure (A.halfImage i : Set ℂ)) := by
  have hmaps : MapsTo closedUpperHalfPlaneModel.symm (closure (A.halfImage i : Set ℂ))
      (A.chart i).target := fun z hz ↦ by
    obtain ⟨x, hx, hxz⟩ := A.exists_mem_closure_dom_of_mem_closure_halfImage hz
    rw [hxz]
    exact (A.chart i).map_source (A.closure_dom_subset_source i hx)
  have hpt : ContinuousOn (fun z ↦ (A.chart i).symm (closedUpperHalfPlaneModel.symm z))
      (closure (A.halfImage i : Set ℂ)) :=
    (A.chart i).continuousOn_symm.comp closedUpperHalfPlaneModel.continuous_symm.continuousOn
      hmaps
  refine (continuous_snd.comp_continuousOn ((A.triv i).continuousOn.comp
    (hs.comp_continuousOn hpt) fun z hz ↦ (A.triv i).mem_source.2
      (A.chart_symm_mem_baseSet_of_mem_closure_halfImage hz))).congr fun z _ ↦ by
      rw [A.halfCoord_def i s z, coord_def]; rfl

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
  {F' : Type*} [TopologicalSpace F'] {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, TopologicalSpace (V' x)] [FiberBundle F' V']

/-- **Chart transitions keep interior points interior.** A point of `M` lying in the domain of chart
`i` of `A`, and read in chart `i'` of a second atlas `A'` at a point of the interior of the image of
that chart, is read in chart `i` at a point of the interior of the image of chart `i`. -/
theorem coe_chart_mem_halfImage (A' : FiniteBundleAtlas ClosedUpperHalfPlane M F' V')
    {i : Fin A.n} {i' : Fin A'.n} {y : ℂ} (hy : y ∈ A'.halfImage i')
    (hi : (A'.chart i').symm (closedUpperHalfPlaneModel.symm y) ∈ A.dom i) :
    (A.chart i ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y)) : ℂ) ∈ A.halfImage i := by
  obtain ⟨hyU, hy0⟩ := A'.mem_halfImage.1 hy
  refine A.mem_halfImage.2 ⟨?_, ?_⟩
  · rw [closedUpperHalfPlaneModel_symm_coe]
    exact A.mem_image.2 ⟨_, hi, rfl⟩
  have he : (A'.chart i').symm ≫ₕ A.chart i ∈ contDiffGroupoid 1 closedUpperHalfPlaneModel :=
    HasGroupoid.compatible (chart_mem_atlas _ _) (chart_mem_atlas _ _)
  have hpos := ClosedUpperHalfPlane.im_pos_iff_of_mem_contDiffGroupoid he one_ne_zero
    (z := closedUpperHalfPlaneModel.symm y)
    ⟨A'.closure_image_subset_target i' (subset_closure hyU), A.dom_subset_chart_source i hi⟩
  rw [coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hy0.le] at hpos
  exact hpos.1 hy0

/-- **Chart transitions between two atlases are differentiable** at the interior points of the
image of chart `i` of `A` lying over the domain of chart `i'` of `A'`. -/
theorem differentiableOn_coe_chart_chart_symm (A' : FiniteBundleAtlas ClosedUpperHalfPlane M F' V')
    (i : Fin A.n) (i' : Fin A'.n) :
    DifferentiableOn ℝ
      (fun z ↦ (A'.chart i' ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)) : ℂ))
      ((A.halfImage i : Set ℂ) ∩
        {z | (A.chart i).symm (closedUpperHalfPlaneModel.symm z) ∈ A'.dom i'}) := by
  have h := (contDiffOn_ext_coord_change (I := closedUpperHalfPlaneModel) (n := 1)
    (A'.center i') (A.center i)).differentiableOn one_ne_zero
  refine h.congr_mono (fun z _ ↦ ?_) fun z hz ↦ ?_
  · simp only [Function.comp_apply, extChartAt_coe_symm, extChartAt_coe,
      closedUpperHalfPlaneModel_apply]
  obtain ⟨hzU, hz'⟩ := hz
  obtain ⟨hzU, hz0⟩ := A.mem_halfImage.1 hzU
  have hzr : z ∈ range closedUpperHalfPlaneModel := by
    rw [range_closedUpperHalfPlaneModel]; exact hz0.le
  simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage,
    extChartAt_target, extChartAt_source, extChartAt_coe_symm, Function.comp_apply]
  exact ⟨⟨A.closure_image_subset_target i (subset_closure hzU), hzr⟩,
    A'.dom_subset_chart_source i' hz'⟩

omit [IsManifold closedUpperHalfPlaneModel 1 M] in
/-- The chart transition from chart `i'` to chart `i`, read in `ℂ`. -/
private theorem halfTransition_eq (i i' : Fin A.n) :
    A.halfTransition i i' =
      fun z ↦ (A.chart i ((A.chart i').symm (closedUpperHalfPlaneModel.symm z)) : ℂ) := by
  funext z
  simp only [halfTransition_def, transition_eq_symm_trans, OpenPartialHomeomorph.coe_trans,
    Function.comp_apply]

omit [IsManifold closedUpperHalfPlaneModel 1 M] in
/-- A point of the interior of the overlap of two charts, read in chart `i'`, lies in the interior
of the image of chart `i'` and over the domain of chart `i`. -/
private theorem halfOverlap_subset (i i' : Fin A.n) :
    A.halfOverlap i i' ⊆ (A.halfImage i' : Set ℂ) ∩
      {z | (A.chart i').symm (closedUpperHalfPlaneModel.symm z) ∈ A.dom i} :=
  fun _ hz ↦ ⟨A.halfOverlap_subset_halfImage i i' hz, (A.symm_mem_dom_of_mem_overlap hz.1).1⟩

/-- Chart transitions carry interior points of the overlap to interior points. -/
theorem halfTransition_mem_halfOverlap {i i' : Fin A.n} {z : ℂ} (hz : z ∈ A.halfOverlap i i') :
    A.halfTransition i i' z ∈ A.halfOverlap i' i := by
  obtain ⟨hzU, hdom⟩ := A.halfOverlap_subset i i' hz
  refine ⟨?_, ?_⟩
  · rw [mem_preimage, symm_halfTransition]
    exact A.transition_mem_overlap hz.1
  rw [halfTransition_eq]
  exact (A.mem_halfImage.1 (A.coe_chart_mem_halfImage A hzU hdom)).2

omit [IsManifold closedUpperHalfPlaneModel 1 M] in
theorem halfTransition_halfTransition {i i' : Fin A.n} {z : ℂ} (hz : z ∈ A.halfOverlap i i') :
    A.halfTransition i' i (A.halfTransition i i' z) = z := by
  rw [halfTransition, symm_halfTransition, A.transition_transition hz.1,
    coe_closedUpperHalfPlaneModel_symm_of_im_nonneg (A.mem_halfOverlap.1 hz).2.le]

/-- Chart transitions are differentiable on the interiors of the overlaps. -/
theorem differentiableOn_halfTransition (i i' : Fin A.n) :
    DifferentiableOn ℝ (A.halfTransition i i') (A.halfOverlap i i') := by
  rw [halfTransition_eq]
  exact (A.differentiableOn_coe_chart_chart_symm A i' i).mono (A.halfOverlap_subset i i')

omit [IsManifold closedUpperHalfPlaneModel 1 M] in
/-- The interior points of the image of chart `i` lying over an open set of `M` form an open set. -/
private theorem isOpen_halfImage_inter_preimage (i : Fin A.n) {D : Set M} (hD : IsOpen D) :
    IsOpen ((A.halfImage i : Set ℂ) ∩
      {y | (A.chart i).symm (closedUpperHalfPlaneModel.symm y) ∈ D}) :=
  ((A.continuousOn_chart_symm i).comp closedUpperHalfPlaneModel.continuous_symm.continuousOn
    fun _ hy ↦ (A.mem_halfImage.1 hy).1).isOpen_inter_preimage (A.halfImage i).isOpen hD

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
  -- Pull back along the chart transition from chart `i'` of `A'` to chart `i` of `A`, whose left
  -- inverse is the transition back, on the open sets of interior points lying over the domain of
  -- the other chart.
  have hleft {y : ℂ} (hdom : (A'.chart i').symm (closedUpperHalfPlaneModel.symm y) ∈ A.dom i) :
      (A.chart i).symm (closedUpperHalfPlaneModel.symm
        (A.chart i ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y)) : ℂ)) =
          (A'.chart i').symm (closedUpperHalfPlaneModel.symm y) := by
    rw [closedUpperHalfPlaneModel_symm_coe, (A.chart i).left_inv (A.dom_subset_chart_source i hdom)]
  have hs := A'.isOpen_halfImage_inter_preimage i' (A.isOpen_dom i)
  have hpull := ae_restrict_comp_of_leftInvOn volume
    (f := fun y ↦ (A.chart i ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y)) : ℂ))
    hs.measurableSet (A.isOpen_halfImage_inter_preimage i (A'.isOpen_dom i')).measurableSet
    (A.differentiableOn_coe_chart_chart_symm A' i i')
    (fun y hy ↦ ⟨A.coe_chart_mem_halfImage A' hy.1 hy.2, by
      rw [mem_ofPred_eq, hleft hy.2]; exact A'.symm_mem_dom (A'.mem_halfImage.1 hy.1).1⟩)
    (fun y hy ↦ by
      obtain ⟨hyU', hy0⟩ := A'.mem_halfImage.1 hy.1
      simp only [hleft hy.2, (A'.chart i').right_inv (A'.closure_image_subset_target i'
        (subset_closure hyU')), coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hy0.le])
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left h)
  rw [ae_restrict_iff' hs.measurableSet] at hpull
  rw [ae_restrict_iff' (A'.halfImage i').isOpen.measurableSet]
  filter_upwards [hpull] with y hy hyU hdom using hy ⟨hyU, hdom⟩

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

/-- On the closure of the interior of the image of chart `i` in `ℂ`, the chart expression of a
section is the image of its value under the trivialization of chart `i`, a linear map. -/
theorem halfCoord_eq_continuousLinearMapAt {i : Fin A.n} {z : ℂ}
    (hz : z ∈ closure (A.halfImage i : Set ℂ)) (s : ∀ x, V x) :
    A.halfCoord i s z = (A.triv i).continuousLinearMapAt ℝ
      ((A.chart i).symm (closedUpperHalfPlaneModel.symm z))
        (s ((A.chart i).symm (closedUpperHalfPlaneModel.symm z))) := by
  rw [halfCoord_def, coord_def, Trivialization.continuousLinearMapAt_apply_of_mem ℝ (A.triv i)
    (A.chart_symm_mem_baseSet_of_mem_closure_halfImage hz)]

/-- On the interior of the overlap of two charts, the coordinates of a section in chart `i'` are
the coordinate change applied to its coordinates in chart `i` at the transition point. -/
theorem halfCoord_eq_coordChange {i i' : Fin A.n} (s : ∀ x, V x) {z : ℂ}
    (hz : z ∈ A.halfOverlap i i') :
    A.halfCoord i' s z = (A.triv i).coordChangeL ℝ (A.triv i')
      ((A.chart i').symm (closedUpperHalfPlaneModel.symm z))
      (A.halfCoord i s (A.halfTransition i i' z)) := by
  rw [halfCoord, halfCoord, symm_halfTransition]
  exact A.coord_eq_coordChange s hz.1

/-- Wherever chart `i'` of `A'` and chart `i` of `A` overlap, the reading of a section in chart
`i'` is the coordinate change of the bundle applied to its reading in chart `i` at the
corresponding point. -/
theorem halfCoord_eq_coordChangeL_halfCoord (A' : FiniteBundleAtlas ClosedUpperHalfPlane M F V)
    {i : Fin A.n} {i' : Fin A'.n} (s : ∀ x, V x) {y : ℂ}
    (hj : (A'.chart i').symm (closedUpperHalfPlaneModel.symm y) ∈ (A'.triv i').baseSet)
    (hi : (A'.chart i').symm (closedUpperHalfPlaneModel.symm y) ∈ A.dom i) :
    A'.halfCoord i' s y = (A.triv i).coordChangeL ℝ (A'.triv i')
      ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y))
      (A.halfCoord i s (A.chart i ((A'.chart i').symm (closedUpperHalfPlaneModel.symm y)))) := by
  rw [halfCoord_def, halfCoord_def, closedUpperHalfPlaneModel_symm_coe]
  exact A.coord_eq_coordChangeL_coord A' s hj hi

/-- On the image of chart `i`, including its points on the real axis, the chart reading of
`x ↦ φ x • s x` is the chart reading of `φ` times that of `s`. -/
theorem halfCoord_fun_smul (i : Fin A.n) (φ : M → ℝ) (s : ∀ x, V x) {z : ℂ}
    (hz : closedUpperHalfPlaneModel.symm z ∈ A.image i) :
    A.halfCoord i (fun x ↦ φ x • s x) z =
      φ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)) • A.halfCoord i s z := by
  rw [halfCoord_def, halfCoord_def]
  exact A.coord_fun_smul i φ s hz

/-- A section vanishing off `L` reads as zero in every chart of `A.focus i hL hLi` other than `i`,
on the interior of its image. -/
theorem halfCoord_focus_eq_zero {i : Fin A.n} {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i)
    {j : Fin A.n} (hj : j ≠ i) {s : ∀ x, V x} (hs : ∀ x ∉ L, s x = 0) {z : ℂ}
    (hz : z ∈ (A.focus i hL hLi).halfImage j) : A.halfCoord j s z = 0 := by
  obtain ⟨hz, -⟩ := (A.focus i hL hLi).mem_halfImage.1 hz
  obtain ⟨x, hx, hxz⟩ := (A.focus i hL hLi).mem_image.1 hz
  rw [chart_focus] at hxz
  have hxL : x ∉ L := fun hxL ↦
    (eq_empty_iff_forall_notMem.1 (A.focus_dom_inter hL hLi hj)) x ⟨hx, hxL⟩
  have hxj := A.focus_dom_subset hL hLi j hx
  rw [halfCoord_def, ← hxz, A.coord_chart s hxj, hs x hxL]
  exact (A.triv j).linear ℝ (A.dom_subset_baseSet j hxj) |>.map_zero

/-- In chart `i`, the section equal to `ψ • G` there reads as `ψ • G` on the chart image, up to the
real axis. -/
theorem halfCoord_smul_chartSection_coe {i : Fin A.n} (ψ : M → ℝ) (G : ℂ → F) {z : ℂ}
    (hz : z ∈ A.halfClosedImage i) :
    A.halfCoord i (fun x ↦ ψ x • A.chartSection i (fun y : ClosedUpperHalfPlane ↦ G y) x) z =
      ψ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)) • G z := by
  obtain ⟨hzi, hz0⟩ := A.mem_halfClosedImage.1 hz
  rw [A.halfCoord_fun_smul i ψ _ hzi, halfCoord_def, coord_chartSection _ hzi,
    coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz0]

/-- **Smooth sections read off one chart.** For a `Cⁿ` function `ψ` on `M` supported in the domain
of chart `i` and a function `G` that is `Cⁿ` on the image `A.halfClosedImage i` of the chart, up to
the real axis, the section equal in chart `i` to `ψ • G` is a `Cⁿ` section, up to the boundary. -/
theorem contMDiff_smul_chartSection_coe {n : WithTop ℕ∞} [IsManifold closedUpperHalfPlaneModel n M]
    [ContMDiffVectorBundle n F V closedUpperHalfPlaneModel] {i : Fin A.n} {ψ : M → ℝ}
    (hψ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) n ψ) (hψi : tsupport ψ ⊆ A.dom i)
    {G : ℂ → F} (hG : ContDiffOn ℝ n G (A.halfClosedImage i)) :
    ContMDiff closedUpperHalfPlaneModel (closedUpperHalfPlaneModel.prod 𝓘(ℝ, F)) n
      fun x ↦ TotalSpace.mk' F x
        (ψ x • A.chartSection i (fun y : ClosedUpperHalfPlane ↦ G y) x) :=
  hψ.contMDiffOn.smul_section_of_tsupport (A.isOpen_dom i) hψi <|
    ((A.triv i).contMDiffOn_section_iff (A.isOpen_dom i) (A.dom_subset_baseSet i)).2 <|
      (hG.contMDiffOn.comp ((contMDiffOn_extChartAt (x := A.center i)).mono
        (A.dom_subset_chart_source i)) fun x hx ↦ by
          rw [mem_preimage, extChartAt_center_apply, coe_mem_halfClosedImage]
          exact A.mem_image.2 ⟨x, hx, rfl⟩).congr fun x hx ↦ by
            rw [triv_chartSection _ hx, Function.comp_apply, extChartAt_center_apply]

/-- A function continuous on the image of chart `i`, transported to chart `i'` by the chart
transition and the coordinate change of the bundle, is continuous on the overlap read in `ℂ`,
including its points on the real axis. -/
theorem continuousOn_coordChange_halfTransition {i i' : Fin A.n} {g : ℂ → F}
    (hg : ContinuousOn g (A.halfClosedImage i)) :
    ContinuousOn (fun z ↦ (A.triv i).coordChangeL ℝ (A.triv i')
        ((A.chart i').symm (closedUpperHalfPlaneModel.symm z)) (g (A.halfTransition i i' z)))
      (closedUpperHalfPlaneModel.symm ⁻¹' A.overlap i i') :=
  (A.continuousOn_coordChange_transition (g := fun y ↦ g y)
    (hg.comp continuous_subtypeVal.continuousOn fun _ hy ↦ A.coe_mem_halfClosedImage.2 hy)).comp
      closedUpperHalfPlaneModel.continuous_symm.continuousOn fun _ hz ↦ hz

/-- **Gluing chart expressions up to the boundary.** Functions `g i`, continuous on the chart
images `A.halfClosedImage i` and related by the coordinate changes of the bundle on the interiors
`A.halfOverlap i i'` of the overlaps, are the chart expressions of a continuous section. The
relations extend by continuity to the points of the overlaps on the real axis. -/
theorem exists_continuous_halfCoord_eqOn {g : Fin A.n → ℂ → F}
    (hg : ∀ i, ContinuousOn (g i) (A.halfClosedImage i))
    (hcompat : ∀ i i', EqOn (g i')
      (fun z ↦ (A.triv i).coordChangeL ℝ (A.triv i')
        ((A.chart i').symm (closedUpperHalfPlaneModel.symm z)) (g i (A.halfTransition i i' z)))
      (A.halfOverlap i i')) :
    ∃ t : ∀ x, V x, Continuous (fun x ↦ TotalSpace.mk' F x (t x)) ∧
      ∀ i, EqOn (A.halfCoord i t) (g i) (A.halfClosedImage i) := by
  -- The relations extend by continuity to the points of the overlaps on the real axis.
  have hcompat' (i i' : Fin A.n) : EqOn (g i')
      (fun z ↦ (A.triv i).coordChangeL ℝ (A.triv i')
        ((A.chart i').symm (closedUpperHalfPlaneModel.symm z)) (g i (A.halfTransition i i' z)))
      (closedUpperHalfPlaneModel.symm ⁻¹' A.overlap i i' ∩ {z : ℂ | 0 ≤ z.im}) :=
    (hcompat i i').of_subset_closure ((hg i').mono fun z hz ↦
        A.mem_halfClosedImage.2 ⟨A.overlap_subset_image i i' hz.1, hz.2⟩)
      ((A.continuousOn_coordChange_halfTransition (hg i)).mono inter_subset_left)
      (fun z hz ↦ ⟨(A.mem_halfOverlap.1 hz).1, (A.mem_halfOverlap.1 hz).2.le⟩)
      (A.subset_closure_halfOverlap i i')
  obtain ⟨t, ht, hteq⟩ := A.exists_continuous_coord_eqOn (g := fun i y ↦ g i y)
    (fun i ↦ (hg i).comp continuous_subtypeVal.continuousOn fun _ hy ↦
      A.coe_mem_halfClosedImage.2 hy) fun i i' y hy ↦ by
      -- A point of the overlap in the closed upper half-plane, read in `ℂ`.
      have hy' : (y : ℂ) ∈
          closedUpperHalfPlaneModel.symm ⁻¹' A.overlap i i' ∩ {z : ℂ | 0 ≤ z.im} :=
        ⟨by rw [mem_preimage, closedUpperHalfPlaneModel_symm_coe]; exact hy, y.property⟩
      simpa only [closedUpperHalfPlaneModel_symm_coe, halfTransition_def] using hcompat' i i' hy'
  refine ⟨t, ht, fun i z hz ↦ ?_⟩
  obtain ⟨hzi, hz0⟩ := A.mem_halfClosedImage.1 hz
  rw [halfCoord_def, hteq i hzi]
  exact congrArg (g i) (coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz0)

end FiniteBundleAtlas

end Linear

end TauCeti
