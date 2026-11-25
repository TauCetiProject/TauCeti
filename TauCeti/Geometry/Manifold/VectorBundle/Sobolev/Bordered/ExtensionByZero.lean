/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Atlas.Transfer

/-!
# Extension by zero from one chart over a surface with boundary

Let `M` be a `Cⁿ` manifold modelled on the closed upper half-plane, for instance a surface with
boundary, let `V → M` be a `Cⁿ` real vector bundle with finite-dimensional model fibre `F`, and
let `A` be a finite bundle atlas. This file supplies the chart-level steps towards the density of
sections smooth up to the boundary in `W^{k,p}(V)` (`TauCeti.BorderedSobolevSection`).

* **Extension by zero.** A section vanishing off a closed set `L` inside the domain of chart `i`,
  whose components in chart `i` are `W^{k,p}` functions on the interior `A.halfImage i` of the chart
  image, has `W^{k,p}` components in every chart of `A`
  (`TauCeti.BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord_of_eq_zero`), for orders
  `k ≤ n`. In the atlas `A.focus i hL hLi`, which removes `L` from the domains of the other charts,
  the section has `W^{k,p}` components in every chart, being zero in all charts but `i`; sections
  then transfer to `A` (`TauCeti.BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord`).
* **Smooth sections from one chart.** For a `Cⁿ` function `ψ` supported in the domain of chart `i`
  and a `Cⁿ` function `G` on `ℂ`, the section equal in chart `i` to `ψ • G` is a `Cⁿ` section, up to
  the boundary (`TauCeti.FiniteBundleAtlas.contMDiff_smul_chartSection_coe`); its reading in
  chart `i` is the product of the readings
  (`TauCeti.FiniteBundleAtlas.halfCoord_smul_chartSection_coe`). With
  `TauCeti.Wkp.mem_closure_range_restrictL_ofTestFunctionₗ_top_upperHalf`, these are the
  approximating sections.

## Main results

* `TauCeti.BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord_of_eq_zero`: extension by
  zero from one chart.
* `TauCeti.FiniteBundleAtlas.contMDiff_smul_chartSection_coe`,
  `TauCeti.FiniteBundleAtlas.halfCoord_smul_chartSection_coe`: smooth sections read off one
  chart.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.1.
* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ENNReal ContDiff

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

namespace FiniteBundleAtlas

variable {A : FiniteBundleAtlas ClosedUpperHalfPlane M F V}

omit [NormedSpace ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- The readings of a section in the charts of `A.focus i hL hLi` are its readings in `A`. -/
theorem halfCoord_focus {i : Fin A.n} {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i)
    (j : Fin A.n) (s : ∀ x, V x) : (A.focus i hL hLi).halfCoord j s = A.halfCoord j s := by
  ext z
  rw [(A.focus i hL hLi).halfCoord_def j s z, A.halfCoord_def j s z,
    (A.focus i hL hLi).coord_def j s, A.coord_def j s]
  -- The charts of `A.focus i hL hLi` have the centres of `A` (`FiniteBundleAtlas.focus_center`).
  rfl

omit [NormedSpace ℝ F] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- The interior of the image of a chart of `A.focus i hL hLi` lies in that of `A`. -/
theorem halfImage_focus_le {i : Fin A.n} {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i)
    (j : Fin A.n) : (A.focus i hL hLi).halfImage j ≤ A.halfImage j := by
  intro z hz
  obtain ⟨hz, hz0⟩ := (A.focus i hL hLi).mem_halfImage.1 hz
  obtain ⟨x, hx, hxz⟩ := (A.focus i hL hLi).mem_image.1 hz
  exact A.mem_halfImage.2 ⟨A.mem_image.2 ⟨x, A.focus_dom_subset hL hLi j hx, by
    simpa only [chart, focus_center] using hxz⟩, hz0⟩

/-- A section vanishing off `L` reads as zero in every chart of `A.focus i hL hLi` other than `i`,
on the interior of its image. -/
theorem halfCoord_focus_eq_zero {i : Fin A.n} {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i)
    {j : Fin A.n} (hj : j ≠ i) {s : ∀ x, V x} (hs : ∀ x ∉ L, s x = 0) {z : ℂ}
    (hz : z ∈ (A.focus i hL hLi).halfImage j) : A.halfCoord j s z = 0 := by
  obtain ⟨hz, -⟩ := (A.focus i hL hLi).mem_halfImage.1 hz
  obtain ⟨x, hx, hxz⟩ := (A.focus i hL hLi).mem_image.1 hz
  have hxL : x ∉ L := fun hxL ↦
    (eq_empty_iff_forall_notMem.1 (A.focus_dom_inter hL hLi j hj)) x ⟨hx, hxL⟩
  have hxj := A.focus_dom_subset hL hLi j hx
  have hxz' : A.chart j x = closedUpperHalfPlaneModel.symm z := by
    simpa only [chart, focus_center] using hxz
  rw [halfCoord_def, ← hxz', A.coord_chart s hxj, hs x hxL]
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
of chart `i` and a `Cⁿ` function `G` on `ℂ`, the section equal in chart `i` to `ψ • G` is a `Cⁿ`
section, up to the boundary. -/
theorem contMDiff_smul_chartSection_coe {n : WithTop ℕ∞} [IsManifold closedUpperHalfPlaneModel n M]
    [ContMDiffVectorBundle n F V closedUpperHalfPlaneModel] {i : Fin A.n} {ψ : M → ℝ}
    (hψ : ContMDiff closedUpperHalfPlaneModel 𝓘(ℝ) n ψ) (hψi : tsupport ψ ⊆ A.dom i)
    {G : ℂ → F} (hG : ContDiff ℝ n G) :
    ContMDiff closedUpperHalfPlaneModel (closedUpperHalfPlaneModel.prod 𝓘(ℝ, F)) n
      fun x ↦ TotalSpace.mk' F x
        (ψ x • A.chartSection i (fun y : ClosedUpperHalfPlane ↦ G y) x) :=
  hψ.contMDiffOn.smul_section_of_tsupport (A.isOpen_dom i) hψi <|
    ((A.triv i).contMDiffOn_section_iff (A.isOpen_dom i) (A.dom_subset_baseSet i)).2 <|
      (hG.contMDiff.comp_contMDiffOn ((contMDiffOn_extChartAt (x := A.center i)).mono
        (A.dom_subset_chart_source i))).congr fun x hx ↦ by
          rw [triv_chartSection _ hx, Function.comp_apply, extChartAt_center_apply]

end FiniteBundleAtlas

namespace BorderedSobolevSection

open FiniteBundleAtlas

variable [FiniteDimensional ℝ F] {n : ℕ} [IsManifold closedUpperHalfPlaneModel n M]
  [ContMDiffVectorBundle n F V closedUpperHalfPlaneModel] {p : ℝ≥0∞} [Fact (1 ≤ p)] {k : ℕ}
  {A : FiniteBundleAtlas ClosedUpperHalfPlane M F V}

/-- **Extension by zero from one chart.** Let `L` be a closed subset of the domain of chart `i` and
`k ≤ n`, `1 ≤ n`. A section vanishing off `L` whose components in chart `i` are `W^{k,p}`
functions on the interior `A.halfImage i` of the chart image has `W^{k,p}` components in every
chart: some element of `W^{k,p}(V)` has chart data equal to its readings. -/
theorem exists_chartValueL_ae_eq_halfCoord_of_eq_zero (hn : 1 ≤ n) (hkn : k ≤ n) {i : Fin A.n}
    {L : Set M} (hL : IsClosed L) (hLi : L ⊆ A.dom i) {s : ∀ x, V x} (hs : ∀ x ∉ L, s x = 0)
    (hv : ∀ m : Fin (finrank ℝ F), ∃ v : Wkp volume (A.halfImage i) p k,
      (Wkp.value k v : ℂ → ℝ) =ᵐ[volume.restrict (A.halfImage i : Set ℂ)]
        fun z ↦ (finBasis ℝ F).coord m (A.halfCoord i s z)) :
    ∃ w : BorderedSobolevSection A p k, ∀ j, A.halfSectionChartData.chartValueL volume p k j w
      =ᵐ[volume.restrict (A.halfImage j : Set ℂ)] A.halfCoord j s := by
  set A' := A.focus i hL hLi
  -- The components in the charts of `A'`: those of chart `i` restricted, and zero elsewhere.
  have hcomp (j : Fin A'.n) (m : Fin (finrank ℝ F)) : ∃ v : Wkp volume (A'.halfImage j) p k,
      (Wkp.value k v : ℂ → ℝ) =ᵐ[volume.restrict (A'.halfImage j : Set ℂ)]
        fun z ↦ (finBasis ℝ F).coord m (A'.halfSectionChartData.coord j s z) := by
    have hcoord := (A'.halfSectionChartData_coord_ae_eq j s).fun_comp ((finBasis ℝ F).coord m)
    rw [show A'.halfCoord j s = A.halfCoord j s from halfCoord_focus hL hLi j s] at hcoord
    by_cases hj : j = i
    · obtain ⟨v, hv⟩ : ∃ v : Wkp volume (A.halfImage j) p k,
          (Wkp.value k v : ℂ → ℝ) =ᵐ[volume.restrict (A.halfImage j : Set ℂ)]
            fun z ↦ (finBasis ℝ F).coord m (A.halfCoord j s z) := by
        rw [hj]; exact hv m
      have hle := A.halfImage_focus_le hL hLi j
      exact ⟨Wkp.restrictL hle k v, (Wkp.value_restrictL_ae hle k v).trans
        (EventuallyEq.trans (ae_restrict_of_ae_restrict_of_subset hle hv) hcoord.symm)⟩
    · refine ⟨0, ?_⟩
      filter_upwards [hcoord, ae_restrict_mem (A'.halfImage j).isOpen.measurableSet,
        Wkp.value_zero_ae (mu := volume) (Omega := A'.halfImage j) (p := p) k] with z hz hzm h0
      simp only [Function.comp_apply] at hz
      rw [h0, Pi.zero_apply, hz, halfCoord_focus_eq_zero hL hLi hj hs hzm, map_zero]
  -- The tuple is an element of `W^{k,p}(V)` for `A'`, which transfers to `A`.
  choose v hv using hcomp
  have hw' : (fun j m ↦ v j m) ∈ A'.halfSectionChartData.sobolevSections volume p k :=
    (SectionChartData.mem_sobolevSections_iff _ _ _ _).2 ⟨s, fun j ↦
      A'.halfSectionChartData.chartValueL_ae_eq_coord volume p k (hv j)⟩
  refine exists_chartValueL_ae_eq_halfCoord hn hkn ⟨_, hw'⟩ (fun j ↦ ?_) A
  exact (A'.halfSectionChartData.chartValueL_ae_eq_coord volume p k (hv j)).trans
    (A'.halfSectionChartData_coord_ae_eq j s)

end BorderedSobolevSection

end TauCeti
