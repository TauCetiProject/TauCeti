/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Perfect
import TauCeti.Topology.OpenPartialHomeomorph.Continuity

/-!
# Transporting local statements through charts

A function `k` on a charted space is read in the preferred chart at `x` as
`k ∘ (chartAt H x).symm`, near the coordinate `chartAt H x x`. This file records how such
representatives transform: under a change of chart, under composition with a continuous map
between charted spaces, and how punctured neighbourhoods are carried by the inverse chart. These
are the facts needed to read a local notion of one variable (meromorphy, orders, ...) on a
charted space in its preferred charts and to check that it is well behaved. Some global properties
of the model space also pass to the charted space: having no isolated points, and, for a Lindelöf
charted space, second countability.

## Main results

* `TauCeti.tendsto_chartAt_symm_nhdsNE`: the inverse of the chart at `x` maps punctured
  neighbourhoods of `chartAt H x x` into punctured neighbourhoods of `x`.
* `TauCeti.tendsto_chartAt_nhdsNE`: conversely, the chart at `x` maps punctured neighbourhoods of
  `x` into punctured neighbourhoods of `chartAt H x x`.
* `TauCeti.comp_symm_eventuallyEq_comp_chartAt_symm_comp`: the representative of `k` in a chart `e`
  at `x` is its representative in the preferred chart composed with the transition map.
* `TauCeti.comp_comp_chartAt_symm_eventuallyEq`: the representative of `k ∘ φ` is the
  representative of `k` composed with the representative of `φ`.
* `ChartedSpace.perfectSpace`: a charted space over a space without isolated points has no
  isolated points.
* `ChartedSpace.secondCountable_of_lindelof`: a Lindelöf charted space over a second-countable
  model space is second countable.
-/

public section

open Filter Topology

namespace TauCeti

variable {H H' X Y : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace X]
  [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] {x : X}

/-- The inverse of the chart at `x` maps punctured neighbourhoods of `chartAt H x x` into
punctured neighbourhoods of `x`. -/
theorem tendsto_chartAt_symm_nhdsNE (x : X) :
    Tendsto (chartAt H x).symm (𝓝[≠] (chartAt H x x)) (𝓝[≠] x) :=
  (chartAt H x).tendsto_symm_nhdsNE (mem_chart_source H x)

/-- The chart at `x` maps punctured neighbourhoods of `x` into punctured neighbourhoods of
`chartAt H x x`. -/
theorem tendsto_chartAt_nhdsNE (x : X) :
    Tendsto (chartAt H x) (𝓝[≠] x) (𝓝[≠] (chartAt H x x)) :=
  (chartAt H x).tendsto_nhdsNE (mem_chart_source H x)

/-- Near `e x`, the representative of `k` in a chart `e` is its representative in the preferred
chart at `x`, composed with the transition map from `e` to that chart. -/
theorem comp_symm_eventuallyEq_comp_chartAt_symm_comp {α : Type*} (k : X → α)
    {e : OpenPartialHomeomorph X H} (hx : x ∈ e.source) :
    k ∘ e.symm =ᶠ[𝓝 (e x)] (k ∘ (chartAt H x).symm) ∘ (chartAt H x ∘ e.symm) := by
  filter_upwards [(e.tendsto_symm hx).eventually (chart_source_mem_nhds H x)] with z hz
  simp [(chartAt H x).left_inv hz]

/-- Near `chartAt H x x`, the representative of `k ∘ φ` is the representative of `k` composed with
the representative of `φ`. -/
theorem comp_comp_chartAt_symm_eventuallyEq {α : Type*} (k : Y → α) {φ : X → Y}
    (hφ : ContinuousAt φ x) :
    (k ∘ φ) ∘ (chartAt H x).symm =ᶠ[𝓝 (chartAt H x x)]
      (k ∘ (chartAt H' (φ x)).symm) ∘ fun z ↦ chartAt H' (φ x) (φ ((chartAt H x).symm z)) := by
  have hcont : Tendsto (fun z ↦ φ ((chartAt H x).symm z)) (𝓝 (chartAt H x x)) (𝓝 (φ x)) :=
    hφ.tendsto.comp ((chartAt H x).tendsto_symm (mem_chart_source H x))
  filter_upwards [hcont.eventually (chart_source_mem_nhds H' (φ x))] with z hz
  simp [(chartAt H' (φ x)).left_inv hz]

section T2

variable [T2Space X]

/-- In a Hausdorff charted space, finitely many distinct points `p i` have pairwise disjoint open
neighbourhoods `V i` inside the domains of the charts at them. -/
theorem exists_pairwise_disjoint_isOpen_subset_chartAt_source {ι : Type*} [Finite ι]
    {p : ι → X} (hinj : Function.Injective p) :
    ∃ V : ι → Set X, (∀ i, IsOpen (V i)) ∧ (∀ i, V i ⊆ (chartAt H (p i)).source) ∧
      (∀ i, p i ∈ V i) ∧ Pairwise (Function.onFun Disjoint V) := by
  obtain ⟨U, hU, hUdisj⟩ := (Set.finite_range p).t2_separation
  refine ⟨fun i => U (p i) ∩ (chartAt H (p i)).source,
    fun i => (hU (p i)).2.inter (chartAt H (p i)).open_source, fun i => Set.inter_subset_right,
    fun i => ⟨(hU (p i)).1, mem_chart_source H (p i)⟩, fun i j hij => ?_⟩
  exact (hUdisj (Set.mem_range_self i) (Set.mem_range_self j) (hinj.ne hij)).mono
    Set.inter_subset_left Set.inter_subset_left

end T2

end TauCeti

/-- A charted space over a space without isolated points has no isolated points: the chart at
`x` sends `x` to a point that is not isolated. -/
theorem ChartedSpace.perfectSpace {H X : Type*} [TopologicalSpace H] [PerfectSpace H]
    [TopologicalSpace X] [ChartedSpace H X] : PerfectSpace X :=
  perfectSpace_iff_forall_not_isolated.2 fun x ↦ (chartAt H x).nhdsNE_neBot (mem_chart_source H x)

/-- A Lindelöf charted space over a second-countable model space is second countable. -/
theorem ChartedSpace.secondCountable_of_lindelof (H X : Type*) [TopologicalSpace H]
    [SecondCountableTopology H] [TopologicalSpace X] [ChartedSpace H X] [LindelofSpace X] :
    SecondCountableTopology X := by
  obtain ⟨s, hsc, hsU⟩ := LindelofSpace.elim_nhds_subcover (fun x : X ↦ (chartAt H x).source)
    fun x ↦ chart_source_mem_nhds H x
  exact ChartedSpace.secondCountable_of_countable_cover H hsU hsc
