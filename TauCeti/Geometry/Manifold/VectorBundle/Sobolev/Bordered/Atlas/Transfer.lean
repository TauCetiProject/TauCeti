/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Basic
import TauCeti.Analysis.Sobolev.Local.ChangeOfVariables.HalfPlaneChart
import TauCeti.Analysis.Sobolev.Local.Locality
import TauCeti.Analysis.Sobolev.Local.Wkp.HalfDisc
import TauCeti.Analysis.Sobolev.Wkp.Restriction

/-!
# Sobolev sections over a surface with boundary in every half-plane chart

Let `M` be a `Cⁿ` manifold modelled on the closed upper half-plane `ClosedUpperHalfPlane`, for
instance a surface with boundary, and let `V → M` be a `Cⁿ` real vector bundle with
finite-dimensional model fibre `F`, for some `n ≥ 1`. The Sobolev space `W^{k,p}(V)` of
`TauCeti.BorderedSobolevSection A p k` is built from a finite bundle atlas `A`: its elements are
tuples of chartwise `W^{k,p}` components of sections, on the interiors in `ℂ` of the images of the
charts of `A`. This file shows, for `1 ≤ p ≤ ∞` and every order `k ≤ n`, that a section with
`W^{k,p}` components in the charts of `A` has `W^{k,p}` components in the charts of every other
finite bundle atlas `B`, with bounds reaching the real axis
(`TauCeti.BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord`).

## The argument

The chart expressions of the section in `A` lie in the half-disc classes
`TauCeti.MemWkpLoc p (A.halfClosedImage i) k`, whose `Lᵖ` bounds reach the real axis
(`TauCeti.BorderedSobolevSection.memWkpLoc_halfCoord`). Near a point of the image of chart `j`
of `B`, read the section in a chart `i` of `A` whose domain contains the corresponding point of
`M`. The change of chart from `j` to `i` is a map between relatively open subsets of the closed
upper half-plane that is `Cⁿ` in both directions, so it preserves the half-disc classes
(`TauCeti.MemWkpLoc.comp_partialEquiv_halfPlane`); the coordinate change of the bundle from `i` to
`j` is a `Cⁿ` field of continuous linear maps up to the real axis, so applying it does too
(`TauCeti.MemWkpLoc.contDiffOn_clm_apply_inter_setOf_im_nonneg`). So the chart expression in
chart `j` lies in the half-disc class on the relatively open part of the target of the extended
chart lying over the base set of the bundle chart
(`TauCeti.FiniteBundleAtlas.memWkpLoc_halfCoord_extChartAt_target`). That set contains the
closure of the interior `B.halfImage j` of the image of the chart, which is compact, so the chart
expression is a `W^{k,p}` function on `B.halfImage j` (`TauCeti.MemWkpLoc.exists_wkp_upperHalf`).

## Main results

* `TauCeti.FiniteBundleAtlas.memWkpLoc_halfCoord_extChartAt_target`: half-disc Sobolev regularity of
  the chart expressions of a section in one finite bundle atlas gives it in every other, on the
  whole chart targets over the bundle charts.
* `TauCeti.BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord`: a section with `W^{k,p}`
  components in the charts of `A` has `W^{k,p}` components in the charts of `B`.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1 and Appendix C.1.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold Topology ENNReal ContDiff

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M] {n : ℕ}
  [IsManifold closedUpperHalfPlaneModel n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle n F V closedUpperHalfPlaneModel]
  {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}

namespace FiniteBundleAtlas

variable (A B : FiniteBundleAtlas ClosedUpperHalfPlane M F V)

omit [FiniteDimensional ℝ F] in
/-- At a point of the target of the extended chart `j` of `B` lying over the source of the chart
`i` of `A` and the base sets of both bundle charts, the reading of a section in chart `j` is the
coordinate change of the bundle applied to its reading in chart `i`. -/
private theorem halfCoord_eq_coordChangeL_halfCoord_extChartAt (s : ∀ x, V x) {i : Fin A.n}
    {j : Fin B.n} {z : ℂ}
    (hzA : (extChartAt closedUpperHalfPlaneModel (B.center j)).symm z ∈ (A.chart i).source)
    (hzb : (extChartAt closedUpperHalfPlaneModel (B.center j)).symm z ∈
      (A.triv i).baseSet ∩ (B.triv j).baseSet) :
    B.halfCoord j s z = (A.triv i).coordChangeL ℝ (B.triv j)
      ((extChartAt closedUpperHalfPlaneModel (B.center j)).symm z)
      (A.halfCoord i s (extChartAt closedUpperHalfPlaneModel (A.center i)
        ((extChartAt closedUpperHalfPlaneModel (B.center j)).symm z))) := by
  have hy : (extChartAt closedUpperHalfPlaneModel (B.center j)).symm z =
      (B.chart j).symm (closedUpperHalfPlaneModel.symm z) := by
    rw [extChartAt_coe_symm]; rfl
  rw [halfCoord_def, halfCoord_def, coord_def, coord_def, extChartAt_coe, Function.comp_apply,
    ModelWithCorners.left_inv, (A.chart i).left_inv hzA, ← hy,
    Trivialization.coordChangeL_apply _ _ hzb, Trivialization.symm_apply_apply_mk _ hzb.1]

omit [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle n F V closedUpperHalfPlaneModel] in
/-- The reading in chart `i` of `A` of a section in the half-disc class, composed with the change
of chart from chart `j` of `B` to chart `i`, is in the local class on the points of the source of
the change of chart that it maps into the image of chart `i`. -/
private theorem memWkpLoc_halfCoord_comp_extChartAt_trans (hn : 1 ≤ n) (hkn : k ≤ n)
    {s : ∀ x, V x} {i : Fin A.n} (hs : MemWkpLoc p (A.halfClosedImage i) k (A.halfCoord i s))
    (j : Fin B.n) :
    MemWkpLoc p (((extChartAt closedUpperHalfPlaneModel (B.center j)).symm.trans
        (extChartAt closedUpperHalfPlaneModel (A.center i))).source ∩
      ((extChartAt closedUpperHalfPlaneModel (B.center j)).symm.trans
        (extChartAt closedUpperHalfPlaneModel (A.center i))) ⁻¹' A.halfOpen i) k
      (fun z ↦ A.halfCoord i s (((extChartAt closedUpperHalfPlaneModel (B.center j)).symm.trans
        (extChartAt closedUpperHalfPlaneModel (A.center i))) z)) := by
  set e : PartialEquiv ℂ ℂ := (extChartAt closedUpperHalfPlaneModel (B.center j)).symm.trans
    (extChartAt closedUpperHalfPlaneModel (A.center i))
  obtain ⟨Ω, hΩ, hΩe⟩ := (B.chart j).exists_isOpen_extend_target_inter_preimage
    (A.chart i).open_source
  obtain ⟨Ω', hΩ', hΩ'e⟩ := (A.chart i).exists_isOpen_extend_target_inter_preimage
    (B.chart j).open_source
  have hs' : e.source = Ω ∩ {z | 0 ≤ z.im} := by
    rw [← hΩe, PartialEquiv.trans_source, extChartAt_source]
    rfl
  have ht' : e.target = Ω' ∩ {z | 0 ≤ z.im} := by
    rw [← hΩ'e, PartialEquiv.trans_target, PartialEquiv.symm_target, extChartAt_source]
    rfl
  have he : ContDiffOn ℝ n e e.source := contDiffOn_ext_coord_change (A.center i) (B.center j)
  have he' : ContDiffOn ℝ n e.symm e.target := by
    have h := contDiffOn_ext_coord_change (I := closedUpperHalfPlaneModel) (n := n) (B.center j)
      (A.center i)
    refine h.congr_mono (fun z _ ↦ rfl) fun z hz ↦ ?_
    simpa only [e, PartialEquiv.trans_target, PartialEquiv.symm_symm, PartialEquiv.trans_source,
      PartialEquiv.symm_source, PartialEquiv.symm_target, mem_inter_iff, mem_preimage] using hz
  exact (hs.congr_mono (fun _ _ ↦ rfl) (A.halfClosedImage_eq_inter i).ge
    |>.comp_partialEquiv_halfPlane hn hkn hΩ hΩ' hs' ht' he he' (A.halfOpen i).isOpen)

/-- **Changes of half-plane chart preserve Sobolev regularity of sections.** If the chart
expressions of a section `s` in the charts of a finite bundle atlas `A` lie in the half-disc
classes `MemWkpLoc p (A.halfClosedImage i) k`, then for every other finite bundle atlas `B` the
chart expression in chart `j` lies in the half-disc class on the part of the target of the extended
chart lying over the base set of the bundle chart. -/
theorem memWkpLoc_halfCoord_extChartAt_target (hn : 1 ≤ n) (hkn : k ≤ n) {s : ∀ x, V x}
    (hs : ∀ i, MemWkpLoc p (A.halfClosedImage i) k (A.halfCoord i s)) (j : Fin B.n) :
    MemWkpLoc p ((extChartAt closedUpperHalfPlaneModel (B.center j)).target ∩
      (extChartAt closedUpperHalfPlaneModel (B.center j)).symm ⁻¹' (B.triv j).baseSet) k
      (B.halfCoord j s) := by
  refine memWkpLoc_iff_locally.2 fun z₀ hz₀ ↦ ?_
  set eB := extChartAt closedUpperHalfPlaneModel (B.center j)
  obtain ⟨hz₀t, hz₀b⟩ := hz₀
  obtain ⟨i, hi⟩ := A.exists_mem_dom (eB.symm z₀)
  set eA := extChartAt closedUpperHalfPlaneModel (A.center i)
  -- The change of chart from `j` to `i`, between relatively open subsets of the half-plane.
  set e : PartialEquiv ℂ ℂ := eB.symm.trans eA
  have hcomp := A.memWkpLoc_halfCoord_comp_extChartAt_trans B hn hkn (hs i) j
  -- The coordinate change of the bundle from `i` to `j`, `Cⁿ` up to the real axis.
  obtain ⟨Ω₀, hΩ₀, hΩ₀e⟩ := (B.chart j).exists_isOpen_extend_target_inter_preimage
    ((A.triv i).open_baseSet.inter (B.triv j).open_baseSet)
  have hC : ContDiffOn ℝ k
      (fun z ↦ ((A.triv i).coordChangeL ℝ (B.triv j) (eB.symm z) : F →L[ℝ] F))
      (Ω₀ ∩ {z | 0 ≤ z.im}) := by
    rw [← hΩ₀e, ← contMDiffOn_iff_contDiffOn]
    exact ((contMDiffOn_coordChangeL (n := n) (A.triv i) (B.triv j)).comp
      ((contMDiffOn_extChartAt_symm (n := n) (B.center j)).mono inter_subset_left)
        fun _ hz ↦ hz.2).of_le (by exact_mod_cast hkn)
  set U : Set ℂ := (e.source ∩ e ⁻¹' A.halfOpen i) ∩
    (eB.target ∩ eB.symm ⁻¹' ((A.triv i).baseSet ∩ (B.triv j).baseSet))
  have hmul := (hcomp.mono inter_subset_left).contDiffOn_clm_apply_inter_setOf_im_nonneg hΩ₀ hC
    (hΩ₀e ▸ inter_subset_right : U ⊆ Ω₀ ∩ {z | 0 ≤ z.im})
  -- On `U`, the reading in chart `j` is the coordinate change of the reading in chart `i`.
  have hchart (y : M) : closedUpperHalfPlaneModel.symm (eA y) = A.chart i y := by
    rw [extChartAt_coe, Function.comp_apply, ModelWithCorners.left_inv]
  refine ⟨U, ?_, hmul.congr fun z hz ↦ ?_⟩
  · -- `U` is a neighbourhood of `z₀` there.
    set O : Set M := A.dom i ∩ ((A.triv i).baseSet ∩ (B.triv j).baseSet)
    have hO : eB.symm ⁻¹' O ∈ 𝓝[eB.target] z₀ :=
      (continuousOn_extChartAt_symm (B.center j) z₀ hz₀t).preimage_mem_nhdsWithin
        (((A.isOpen_dom i).inter ((A.triv i).open_baseSet.inter (B.triv j).open_baseSet)).mem_nhds
          ⟨hi, A.dom_subset_baseSet i hi, hz₀b⟩)
    refine mem_of_superset (inter_mem self_mem_nhdsWithin
      (nhdsWithin_mono _ inter_subset_left hO)) fun z ⟨⟨hz, _⟩, hzO⟩ ↦ ?_
    have hzA : eB.symm z ∈ (A.chart i).source := A.dom_subset_chart_source i hzO.1
    refine ⟨⟨⟨hz, by rw [extChartAt_source]; exact hzA⟩, ?_⟩, hz, hzO.2⟩
    rw [mem_preimage, SetLike.mem_coe, mem_halfOpen, PartialEquiv.coe_trans, Function.comp_apply,
      hchart]
    exact A.mem_image.2 ⟨_, hzO.1, rfl⟩
  · obtain ⟨⟨⟨-, hzA⟩, -⟩, -, hzb⟩ := hz
    rw [extChartAt_source] at hzA
    exact halfCoord_eq_coordChangeL_halfCoord_extChartAt A B s hzA hzb

end FiniteBundleAtlas

namespace BorderedSobolevSection

variable {A : FiniteBundleAtlas ClosedUpperHalfPlane M F V}

/-- **Sobolev sections over a surface with boundary in every finite bundle atlas.** If the chart
data of an element `w` of `W^{k,p}(V)` for the finite bundle atlas `A` are the readings of a
section `s`, then for every other finite bundle atlas `B` some element of `W^{k,p}(V)` for `B` has
chart data equal to the readings of `s` in the charts of `B`. -/
theorem exists_chartValueL_ae_eq_halfCoord (hn : 1 ≤ n) (hkn : k ≤ n)
    (w : BorderedSobolevSection A p k) {s : ∀ x, V x}
    (hs : ∀ i, A.halfSectionChartData.chartValueL volume p k i w
      =ᵐ[volume.restrict (A.halfImage i : Set ℂ)] A.halfCoord i s)
    (B : FiniteBundleAtlas ClosedUpperHalfPlane M F V) :
    ∃ w' : BorderedSobolevSection B p k, ∀ j, B.halfSectionChartData.chartValueL volume p k j w'
      =ᵐ[volume.restrict (B.halfImage j : Set ℂ)] B.halfCoord j s := by
  have hloc := A.memWkpLoc_halfCoord_extChartAt_target B hn hkn (memWkpLoc_halfCoord w hs)
  -- Each component of the reading in chart `j` is a `W^{k,p}` function on `B.halfImage j`.
  have hcomp (j : Fin B.n) (m : Fin (finrank ℝ F)) : ∃ v : Wkp volume (B.halfImage j) p k,
      (Wkp.value k v : ℂ → ℝ) =ᵐ[volume.restrict (B.halfImage j : Set ℂ)]
        fun z ↦ (finBasis ℝ F).coord m (B.halfSectionChartData.coord j s z) := by
    obtain ⟨Ω, hΩ, hΩe⟩ := (B.chart j).exists_isOpen_extend_target_inter_preimage
      (B.triv j).open_baseSet
    have hcl : closure (B.halfImage j : Set ℂ) ⊆ Ω := fun z hz ↦ by
      obtain ⟨x, hx, rfl⟩ := closure_minimal (B.halfImage_subset_extChartAt_image_closure_dom j)
        (B.isCompact_extChartAt_image_closure_dom j).isClosed hz
      have hxs : x ∈ (extChartAt closedUpperHalfPlaneModel (B.center j)).source := by
        rw [extChartAt_source]; exact B.closure_dom_subset_source j hx
      refine (hΩe.subset ⟨(extChartAt closedUpperHalfPlaneModel (B.center j)).map_source hxs,
        ?_⟩ : _ ∈ Ω ∩ {z | 0 ≤ z.im}).1
      change (extChartAt closedUpperHalfPlaneModel (B.center j)).symm _ ∈ (B.triv j).baseSet
      rw [(extChartAt closedUpperHalfPlaneModel (B.center j)).left_inv hxs]
      exact B.closure_dom_subset_baseSet j hx
    have hle : B.halfImage j ≤ (B.halfImage j).upperHalf :=
      fun z hz ↦ Opens.mem_upperHalf.2 ⟨hz, (B.mem_halfImage.1 hz).2⟩
    obtain ⟨v, hv⟩ := ((hloc j).clm_comp (LinearMap.toContinuousLinearMap
      ((finBasis ℝ F).coord m))).congr_mono (fun _ _ ↦ rfl) hΩe.ge
        |>.exists_wkp_upperHalf (Ω := ⟨Ω, hΩ⟩) (B.isCompact_closure_halfImage j) hcl
    exact ⟨Wkp.restrictL hle k v, (Wkp.value_restrictL_ae hle k v).trans
      (EventuallyEq.trans (ae_restrict_of_ae_restrict_of_subset hle hv)
        ((B.halfSectionChartData_coord_ae_eq j s).fun_comp _).symm)⟩
  choose v hv using hcomp
  refine ⟨⟨fun j m ↦ v j m, (SectionChartData.mem_sobolevSections_iff _ _ _ _).2 ⟨s, fun j ↦
    B.halfSectionChartData.chartValueL_ae_eq_coord volume p k (hv j)⟩⟩, fun j ↦ ?_⟩
  exact (B.halfSectionChartData.chartValueL_ae_eq_coord volume p k (hv j)).trans
    (B.halfSectionChartData_coord_ae_eq j s)

end BorderedSobolevSection

end TauCeti
