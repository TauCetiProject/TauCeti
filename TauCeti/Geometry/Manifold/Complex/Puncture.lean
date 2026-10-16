/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Topology.Connected.Puncture
public import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# Punctures of complex-charted spaces

A finite set does not disconnect a connected space locally modelled on the complex plane.

This is the topological input for restricting a map of connected Riemann surfaces away from
finitely many fibres: the remaining open surface is still path-connected.

## Main declarations

* `exists_mem_nhds_isConnected_diff_singleton_of_chartedSpace_complex`: every point of a
  complex-charted space has a neighbourhood that stays connected once the point is removed.
* `isConnected_compl_singleton_of_chartedSpace_complex`: removing one point from a connected
  complex-charted space leaves it connected.
* `Set.Finite.isPathConnected_compl_of_chartedSpace_complex`: the complement of a finite set in a
  connected complex-charted space is path-connected.
-/

public section

open Metric Set Topology

open scoped Manifold

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [ConnectedSpace X]

omit [ConnectedSpace X] in
/-- Every point `p` of a space charted over `ℂ` has a neighbourhood `U` for which the punctured
neighbourhood `U \ {p}` is connected. -/
theorem exists_mem_nhds_isConnected_diff_singleton_of_chartedSpace_complex (p : X) :
    ∃ U ∈ 𝓝 p, IsConnected (U \ {p}) := by
  -- Pull back a punctured coordinate ball around `p` through the chart at `p`.
  let e := chartAt ℂ p
  have htarget : e.target ∈ 𝓝 (e p) := e.open_target.mem_nhds (e.map_source (mem_chart_source ℂ p))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp htarget
  let U : Set X := e.source ∩ e ⁻¹' ball (e p) r
  refine ⟨U, Filter.inter_mem (e.open_source.mem_nhds (mem_chart_source ℂ p))
    (e.continuousAt (mem_chart_source ℂ p) (ball_mem_nhds _ hr)), ?_⟩
  have hball : IsPathConnected (ball (e p) r \ {e p}) := by
    let _ := pathConnectedSpace_ball_diff_singleton (e p) hr
    exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have himage : e.symm '' (ball (e p) r \ {e p}) = U \ {p} := by
    have hsingle : {e p} ⊆ ball (e p) r := singleton_subset_iff.mpr (mem_ball_self hr)
    rw [(e.symm.injOn.mono hrsub).image_sdiff_subset hsingle,
      e.symm_image_eq_source_inter_preimage hrsub]
    simp only [image_singleton, e.left_inv (mem_chart_source ℂ p)]
    rfl
  rw [← himage]
  exact hball.isConnected.image _ (e.symm.continuousOn.mono fun _ hy ↦ hrsub hy.1)

/-- Removing one point from a connected space charted over `ℂ` leaves a connected space. -/
theorem isConnected_compl_singleton_of_chartedSpace_complex (p : X) :
    IsConnected ({p}ᶜ : Set X) := by
  let _ := ChartedSpace.t1Space ℂ X
  obtain ⟨U, hU, hUp⟩ := exists_mem_nhds_isConnected_diff_singleton_of_chartedSpace_complex p
  exact isConnected_compl_singleton_of_mem_nhds p hU hUp

end TauCeti

namespace Set.Finite

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [ConnectedSpace X]

/-- The complement of a finite set in a connected space charted over `ℂ` is connected. -/
theorem isConnected_compl_of_chartedSpace_complex {s : Set X} (hs : s.Finite) :
    IsConnected sᶜ := by
  let _ := ChartedSpace.t1Space ℂ X
  -- Remove the points one at a time, each inside the open complement of the points already
  -- removed, which is again a connected complex-charted space.
  induction s, hs using Set.Finite.induction_on with
  | empty => simpa using (isConnected_univ : IsConnected (univ : Set X))
  | @insert p s hp hs ih =>
      let Y := ↥sᶜ
      let _ : ConnectedSpace Y := isConnected_iff_connectedSpace.mp ih
      have hsopen : IsOpen (sᶜ : Set X) := hs.isClosed.isOpen_compl
      let _ : ChartedSpace X Y := hsopen.isOpenEmbedding_subtypeVal.singletonChartedSpace
      let _ : ChartedSpace ℂ Y := ChartedSpace.comp ℂ X Y
      let p' : Y := ⟨p, by simpa using hp⟩
      have hpunctured : IsConnected ({p'}ᶜ : Set Y) :=
        TauCeti.isConnected_compl_singleton_of_chartedSpace_complex p'
      have himage : ((↑) : Y → X) '' ({p'}ᶜ : Set Y) = (insert p s)ᶜ := by
        ext x
        simp [p']
      rw [← himage]
      exact hpunctured.image ((↑) : Y → X) continuous_subtype_val.continuousOn

/-- The complement of a finite set in a connected space charted over `ℂ` is path-connected. -/
theorem isPathConnected_compl_of_chartedSpace_complex {s : Set X} (hs : s.Finite) :
    IsPathConnected sᶜ := by
  let _ := ChartedSpace.t1Space ℂ X
  have hsopen : IsOpen (sᶜ : Set X) := hs.isClosed.isOpen_compl
  let Y := ↥sᶜ
  let _ : ConnectedSpace Y :=
    isConnected_iff_connectedSpace.mp hs.isConnected_compl_of_chartedSpace_complex
  let _ : ChartedSpace X Y := hsopen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let _ : ChartedSpace ℂ Y := ChartedSpace.comp ℂ X Y
  let _ : LocallyPathConnectedSpace Y := ChartedSpace.locallyPathConnectedSpace ℂ Y
  let _ : PathConnectedSpace Y := PathConnectedSpace.of_locallyPathConnectedSpace
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

end Set.Finite
