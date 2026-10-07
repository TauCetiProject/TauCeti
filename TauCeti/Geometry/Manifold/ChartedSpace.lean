/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# Transporting local statements through charts

A function `k` on a charted space is read in the preferred chart at `x` as
`k ∘ (chartAt H x).symm`, near the coordinate `chartAt H x x`. This file records how such
representatives transform: under a change of chart, under composition with a continuous map
between charted spaces, and how punctured neighbourhoods are carried by the inverse chart. These
are the facts needed to read a local notion of one variable (meromorphy, orders, ...) on a
charted space in its preferred charts and to check that it is well behaved.

## Main results

* `TauCeti.tendsto_chartAt_symm_nhdsNE`: the inverse of the chart at `x` maps punctured
  neighbourhoods of `chartAt H x x` into punctured neighbourhoods of `x`.
* `TauCeti.comp_symm_eventuallyEq_comp_chartAt_symm_comp`: the representative of `k` in a chart `e`
  at `x` is its representative in the preferred chart composed with the transition map.
* `TauCeti.comp_comp_chartAt_symm_eventuallyEq`: the representative of `k ∘ φ` is the
  representative of `k` composed with the representative of `φ`.
-/

public section

open Filter Topology

namespace TauCeti

variable {H H' X Y : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace X]
  [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y] {x : X}

/-- The inverse of the chart at `x` maps punctured neighbourhoods of `chartAt H x x` into
punctured neighbourhoods of `x`. -/
theorem tendsto_chartAt_symm_nhdsNE (x : X) :
    Tendsto (chartAt H x).symm (𝓝[≠] (chartAt H x x)) (𝓝[≠] x) := by
  have hx := mem_chart_source H x
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (((chartAt H x).tendsto_symm hx).mono_left nhdsWithin_le_nhds) ?_
  simpa [(chartAt H x).left_inv hx] using
    (chartAt H x).symm.eventually_ne_nhdsWithin ((chartAt H x).map_source hx)

/-- Near `e x`, the representative of `k` in a chart `e` is its representative in the preferred
chart at `x`, composed with the transition map from `e` to that chart. -/
theorem comp_symm_eventuallyEq_comp_chartAt_symm_comp {α : Type*} (k : X → α)
    {e : OpenPartialHomeomorph X H} (hx : x ∈ e.source) :
    k ∘ e.symm =ᶠ[𝓝 (e x)] (k ∘ (chartAt H x).symm) ∘ (chartAt H x ∘ e.symm) := by
  filter_upwards [(e.tendsto_symm hx).eventually
    ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))] with z hz
  simp [(chartAt H x).left_inv hz]

/-- Near `chartAt H x x`, the representative of `k ∘ φ` is the representative of `k` composed with
the representative of `φ`. -/
theorem comp_comp_chartAt_symm_eventuallyEq {α : Type*} (k : Y → α) {φ : X → Y}
    (hφ : ContinuousAt φ x) :
    (k ∘ φ) ∘ (chartAt H x).symm =ᶠ[𝓝 (chartAt H x x)]
      (k ∘ (chartAt H' (φ x)).symm) ∘ fun z ↦ chartAt H' (φ x) (φ ((chartAt H x).symm z)) := by
  have hcont : Tendsto (fun z ↦ φ ((chartAt H x).symm z)) (𝓝 (chartAt H x x)) (𝓝 (φ x)) :=
    hφ.tendsto.comp ((chartAt H x).tendsto_symm (mem_chart_source H x))
  filter_upwards [hcont.eventually
    ((chartAt H' (φ x)).open_source.mem_nhds (mem_chart_source H' (φ x)))] with z hz
  simp [(chartAt H' (φ x)).left_inv hz]

end TauCeti
