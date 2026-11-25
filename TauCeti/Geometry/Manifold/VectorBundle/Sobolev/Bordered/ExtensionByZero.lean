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
* **Smooth sections from one chart.** The approximating sections are the sections equal in one
  chart to `ψ • G`, for a cutoff `ψ` and a function `G` smooth up to the real axis
  (`TauCeti.FiniteBundleAtlas.contMDiff_smul_chartSection_coe` and
  `TauCeti.FiniteBundleAtlas.halfCoord_smul_chartSection_coe`, in
  `TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.HalfPlane`), with `G` given by
  `TauCeti.Wkp.mem_closure_range_restrictL_ofTestFunctionₗ_top_upperHalf`.

## Main results

* `TauCeti.BorderedSobolevSection.exists_chartValueL_ae_eq_halfCoord_of_eq_zero`: extension by
  zero from one chart.

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
    rw [show A'.halfCoord j s = A.halfCoord j s from A.halfCoord_focus hL hLi j s] at hcoord
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
      rw [h0, Pi.zero_apply, hz, A.halfCoord_focus_eq_zero hL hLi hj hs hzm, map_zero]
  -- The tuple is an element of `W^{k,p}(V)` for `A'`, which transfers to `A`.
  obtain ⟨w', hw'⟩ := exists_chartValueL_ae_eq_halfCoord_of_forall_exists_wkp hcomp
  exact exists_chartValueL_ae_eq_halfCoord hn hkn w' hw' A

end BorderedSobolevSection

end TauCeti
