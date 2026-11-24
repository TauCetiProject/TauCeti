/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import TauCeti.Analysis.Sobolev.Local.Coordinates
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.HalfPlane
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Analysis.Sobolev.Local.Wkp
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
`A : TauCeti.FiniteBundleAtlas ClosedUpperHalfPlane M F V`, read in `ℂ` as in
`TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.HalfPlane`. The image of chart `i` is a
relatively open subset of the closed upper half-plane; in `ℂ` it is
`A.halfClosedImage i = Ω ∩ {0 ≤ im}` for an open set `Ω`, and its interior is the open set
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
(`TauCeti.FiniteBundleAtlas.halfTransition_mem_halfOverlap`) and are `C¹` on the interiors of the
overlaps (`TauCeti.FiniteBundleAtlas.differentiableOn_halfTransition`). So the space is complete
(`TauCeti.BorderedSobolevSection.instCompleteSpace`).

A `Cᵏ` section has `Cᵏ` chart coordinates up to the real axis, so their derivatives through order
`k` are bounded on the chart images, which are relatively compact; this gives the injective linear
map `TauCeti.BorderedSobolevSection.ofContMDiffSection` from `Cᵏ` sections, with a norm bound.
Conversely, the chart expression of every element lies in the local Sobolev class
`MemWkpLoc p (A.halfClosedImage i) k`, whose `Lᵖ` bounds reach the real axis
(`TauCeti.BorderedSobolevSection.memWkpLoc_halfCoord`).

## Main definitions

* `TauCeti.FiniteBundleAtlas.halfSectionChartData`: the chart data on the interiors of the chart
  images.
* `TauCeti.BorderedSobolevSection A p k`: the Banach space `W^{k,p}(V)`.
* `TauCeti.BorderedSobolevSection.ofContMDiffSection`: `Cᵏ` sections as Sobolev sections.

## Main results

* `TauCeti.FiniteBundleAtlas.aeTransition_halfSectionChartData`: chart transitions preserve null
  sets.
* `TauCeti.FiniteBundleAtlas.isFiniteMeasure_restrict_halfImage`: the interiors of the chart images
  have finite measure.
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

section Linear

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

namespace FiniteBundleAtlas

variable (A : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

open Classical in
/-- The chart data of a finite bundle atlas over a base with boundary: a section is read in chart
`i` as `A.halfCoord i s` on the interior `A.halfImage i` of the image of the chart in `ℂ` and on the
images of the overlaps under the chart transitions to chart `i`, and as `0` elsewhere. At each
point the gluing of a family of functions is read off from the function of any chart containing
the point. -/
@[expose] def halfSectionChartData : SectionChartData ℂ F (∀ x, V x) where
  n := A.n
  image := A.halfImage
  overlap := A.halfOverlap
  isOpen_overlap := A.isOpen_halfOverlap
  overlap_subset_image := A.halfOverlap_subset_halfImage
  transition i i' := (A.halfOverlap i i').piecewise (A.halfTransition i i') id
  coordChange i i' := (A.halfOverlap i i').piecewise (fun z ↦
    (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm (closedUpperHalfPlaneModel.symm z)))
    1
  coord i s :=
    ((A.halfImage i : Set ℂ) ∪ ⋃ i', A.halfTransition i i' '' A.halfOverlap i i').indicator
      (A.halfCoord i s)
  transition_of_notMem _ _ _ hz := piecewise_eq_of_notMem _ _ _ hz
  coordChange_of_notMem _ _ _ hz := piecewise_eq_of_notMem _ _ _ hz
  coord_of_notMem _ _ _ hz := indicator_of_notMem (by
    simpa only [(piecewise_eqOn _ _ _).image_eq] using hz) _
  coord_add i s t _ hz := by
    simp only [indicator_of_mem (mem_union_left _ hz), halfCoord_def]
    exact A.coord_add i s t (A.mem_halfImage.1 hz).1
  coord_smul i c s _ hz := by
    simp only [indicator_of_mem (mem_union_left _ hz), halfCoord_def]
    exact A.coord_smul i c s (A.mem_halfImage.1 hz).1
  coord_eq_coordChange i i' s _ hz := by
    rw [piecewise_eq_of_mem _ _ _ hz, piecewise_eq_of_mem _ _ _ hz,
      indicator_of_mem (mem_union_left _ (A.halfOverlap_subset_halfImage i i' hz)),
      indicator_of_mem (mem_union_right _ (mem_iUnion.2 ⟨i', mem_image_of_mem _ hz⟩))]
    exact A.halfCoord_eq_coordChange s hz
  exists_glue f := by
    classical
    let idx : M → Fin A.n := fun x ↦ (A.exists_mem_dom x).choose
    have hidx (x : M) : x ∈ A.dom (idx x) := (A.exists_mem_dom x).choose_spec
    refine ⟨fun x ↦ (A.triv (idx x)).symm x (f (idx x) (A.chart (idx x) x : ℂ)),
      fun i' z hz ↦ ?_⟩
    obtain ⟨hzU, hz0⟩ := A.mem_halfImage.1 hz
    obtain ⟨x, hx, hxz⟩ := A.mem_image.1 hzU
    have hz' : z = (A.chart i' x : ℂ) := by
      rw [hxz, coe_closedUpperHalfPlaneModel_symm_of_im_nonneg hz0.le]
    have hov : z ∈ A.halfOverlap (idx x) i' :=
      A.mem_halfOverlap.2 ⟨by rw [← hxz]; exact A.chart_mem_overlap (hidx x) hx, hz0⟩
    refine ⟨idx x, hov, ?_⟩
    rw [piecewise_eq_of_mem _ _ _ hov, piecewise_eq_of_mem _ _ _ hov,
      indicator_of_mem (mem_union_left _ hz), A.halfCoord_eq_coordChange _ hov, hz',
      A.halfTransition_coe_chart hx, A.halfCoord_coe_chart _ (hidx x),
      (A.triv (idx x)).apply_mk_symm (A.dom_subset_baseSet _ (hidx x))]
    rfl

theorem halfSectionChartData_transition_of_mem {i i' : Fin A.n} {z : ℂ}
    (hz : z ∈ A.halfOverlap i i') :
    A.halfSectionChartData.transition i i' z = A.halfTransition i i' z := by
  classical
  exact piecewise_eq_of_mem _ _ _ hz

theorem halfSectionChartData_coordChange_of_mem {i i' : Fin A.n} {z : ℂ}
    (hz : z ∈ A.halfOverlap i i') :
    A.halfSectionChartData.coordChange i i' z =
      (A.triv i).coordChangeL ℝ (A.triv i')
        ((A.chart i').symm (closedUpperHalfPlaneModel.symm z)) := by
  classical
  simp only [halfSectionChartData, piecewise_eq_of_mem _ _ _ hz]

theorem halfSectionChartData_coord_of_mem {i : Fin A.n} (s : ∀ x, V x) {z : ℂ}
    (hz : z ∈ A.halfImage i) : A.halfSectionChartData.coord i s z = A.halfCoord i s z :=
  indicator_of_mem (mem_union_left _ hz) _

/-- Almost everywhere on the interior of the image of chart `i`, a section is read in the chart
data of the atlas as `A.halfCoord i s`. -/
theorem halfSectionChartData_coord_ae_eq (i : Fin A.n) (s : ∀ x, V x) :
    A.halfSectionChartData.coord i s =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
      A.halfCoord i s := by
  filter_upwards [ae_restrict_mem (A.halfImage i).isOpen.measurableSet] with z hz
  exact A.halfSectionChartData_coord_of_mem s hz

/-- The interior of the image of chart `i` has finite Lebesgue measure, since it lies in the
compact image of the closure of the chart domain. -/
instance isFiniteMeasure_restrict_halfImage (i : Fin A.n) :
    IsFiniteMeasure (volume.restrict (A.halfImage i : Set ℂ)) :=
  isFiniteMeasure_restrict.2
    ((measure_mono (A.halfImage_subset_extChartAt_image_closure_dom i)).trans_lt
      (A.isCompact_extChartAt_image_closure_dom i).measure_lt_top).ne

/-- The image of chart `i` in the chart data `A.halfSectionChartData` has finite Lebesgue
measure. -/
instance isFiniteMeasure_restrict_halfSectionChartData_image (i : Fin A.halfSectionChartData.n) :
    IsFiniteMeasure (volume.restrict (A.halfSectionChartData.image i : Set ℂ)) :=
  A.isFiniteMeasure_restrict_halfImage i

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
    [IsManifold closedUpperHalfPlaneModel 1 M] : A.halfSectionChartData.AETransition volume := by
  refine A.halfSectionChartData.aeTransition_of_differentiableOn
    (fun i i' ↦ (A.differentiableOn_halfTransition i i').congr fun _ hz ↦
      A.halfSectionChartData_transition_of_mem hz) (fun _ _ _ hz ↦ ?_) fun _ _ _ hz ↦ ?_
  · rw [A.halfSectionChartData_transition_of_mem hz]
    exact A.halfTransition_mem_halfOverlap hz
  · rw [A.halfSectionChartData_transition_of_mem hz,
      A.halfSectionChartData_transition_of_mem (A.halfTransition_mem_halfOverlap hz)]
    exact A.halfTransition_halfTransition hz

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
        fun z ↦ (finBasis ℝ F).coord j (A.halfSectionChartData.coord i s z) := by
  have hf := contDiffOn_coord_halfCoord A k s i j
  suffices h : ∃ w : Wkp volume (A.halfImage i) p k, (Wkp.value k w : ℂ → ℝ)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        fun z ↦ (finBasis ℝ F).coord j (A.halfCoord i s z) by
    obtain ⟨w, hw⟩ := h
    exact ⟨w, hw.trans ((A.halfSectionChartData_coord_ae_eq i s).fun_comp _).symm⟩
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

/-- The chart data in chart `i` of the Sobolev section of a `Cᵏ` section `s` are the chart
coordinates `A.halfCoord i s`, almost everywhere on the interior of the image of the chart. -/
theorem chartValueL_ofContMDiffSection_ae (s : Cₛ^k⟮closedUpperHalfPlaneModel; F, V⟯)
    (i : Fin A.n) :
    A.halfSectionChartData.chartValueL volume p k i (ofContMDiffSection A p k s)
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s :=
  (A.halfSectionChartData.chartValueL_ofComponents_ae volume p k _ _ s i).trans
    (A.halfSectionChartData_coord_ae_eq i s)

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
      ((A.halfSectionChartData.value_ofComponents_ae volume p k _ _ s i j).trans
        ((A.halfSectionChartData_coord_ae_eq i s).fun_comp _))

/-- **Injectivity.** A `Cᵏ` section whose Sobolev section vanishes is zero: its chart coordinates
vanish almost everywhere on the interiors of the chart images, hence everywhere there by
continuity, and hence also on the real axis, whose points are limits of interior points. -/
theorem ofContMDiffSection_injective : Function.Injective (ofContMDiffSection A p k) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs ↦ ContMDiffSection.ext fun x ↦ ?_
  obtain ⟨i, hx⟩ := A.exists_mem_dom x
  have hcont : ContinuousOn (A.halfCoord i s) (A.halfChartSet i) :=
    (A.contDiffOn_halfCoord s.contMDiff i).continuousOn
  have hae : A.halfCoord i s =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] 0 :=
    (A.halfSectionChartData_coord_ae_eq i s).symm.trans
      (A.halfSectionChartData.coord_ae_eq_zero_of_ofComponents_eq_zero volume p k _ _ hs i)
  have hzero : EqOn (A.halfCoord i s) 0 (A.halfImage i) :=
    Measure.eqOn_open_of_ae_eq hae (A.halfImage i).isOpen
      (hcont.mono (A.halfImage_subset_halfChartSet i)) continuousOn_const
  -- The point `chart i x` of `ℂ` is a limit of interior points of the chart image.
  have hmem : (A.chart i x : ℂ) ∈ A.halfClosedImage i := by
    rw [halfClosedImage_eq_image_val]
    exact mem_image_of_mem _ (A.mem_image.2 ⟨x, hx, rfl⟩)
  have hK : (A.chart i x : ℂ) ∈ A.halfChartSet i :=
    A.extChartAt_image_closure_dom_subset_halfChartSet i
      ⟨x, subset_closure hx, A.extChartAt_center_apply i x⟩
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

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {A : FiniteBundleAtlas ClosedUpperHalfPlane M F V} {k : ℕ}

namespace BorderedSobolevSection

open FiniteBundleAtlas

/-- **Localization up to the boundary.** If the chart data of an element `w` of `W^{k,p}(V)` are
the coordinates of the section `s`, then in every chart `i` the chart expression `A.halfCoord i s`
lies in the local Sobolev class `MemWkpLoc p (A.halfClosedImage i) k` on the image of the chart in
the closed upper half-plane, with `Lᵖ` bounds on compact sets reaching the real axis. -/
theorem memWkpLoc_halfCoord (w : BorderedSobolevSection A p k) {s : ∀ x, V x}
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (i : Fin A.n) : MemWkpLoc p (A.halfClosedImage i) k (A.halfCoord i s) :=
  (finBasis ℝ F).memWkpLoc_iff.2 fun j ↦
    (Wkp.memWkpLoc_value_of_ae_le (A.interior_halfClosedImage i)
      (A.halfClosedImage_ae_le_halfImage i) _).congr_ae
        (ae_mono (Measure.restrict_mono_ae (A.halfClosedImage_ae_le_halfImage i))
          (((A.halfSectionChartData.chartValueL_ae_eq_coord_iff volume p k).1
            ((hs i).trans (A.halfSectionChartData_coord_ae_eq i s).symm) j).trans
              ((A.halfSectionChartData_coord_ae_eq i s).fun_comp _)))

/-- **Localization up to the boundary.** Every element of `W^{k,p}(V)` consists of the components
of a section whose chart expression in every chart `i` lies in the local Sobolev class
`MemWkpLoc p (A.halfClosedImage i) k`. -/
theorem exists_section_memWkpLoc (w : BorderedSobolevSection A p k) :
    ∃ s : ∀ x, V x, (∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s) ∧
        ∀ i, MemWkpLoc p (A.halfClosedImage i) k (A.halfCoord i s) := by
  obtain ⟨s, hs⟩ := A.halfSectionChartData.exists_section volume p k w
  have hs' (i : Fin A.n) := (hs i).trans (A.halfSectionChartData_coord_ae_eq i s)
  exact ⟨s, hs', memWkpLoc_halfCoord w hs'⟩

end BorderedSobolevSection

end Localization

end TauCeti
