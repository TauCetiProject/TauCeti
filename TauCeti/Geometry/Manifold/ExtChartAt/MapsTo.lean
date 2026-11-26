/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Balls mapped into an extended chart source

Two maps from a pseudometric space into a manifold which are continuous at a point `x₀` and agree
there both send a small ball around `x₀`, inside any given neighbourhood of `x₀`, into the source
of the extended chart at their common value
(`TauCeti.exists_ball_subset_mapsTo_extChartAt_source`). On such a ball the two maps can be
compared through their coordinate expressions in that one chart.
-/

public section

open Set Topology

namespace TauCeti

variable {𝕜 E H M X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] [PseudoMetricSpace X]

/-- Let `u` and `v` be continuous at `x₀` with `u x₀ = v x₀`, and let `s` be a neighbourhood of
`x₀`. Some ball around `x₀` lies in `s` and is mapped by both `u` and `v` into the source of the
extended chart at `u x₀`. -/
theorem exists_ball_subset_mapsTo_extChartAt_source {s : Set X} {u v : X → M} {x₀ : X}
    (hs : s ∈ 𝓝 x₀) (hu : ContinuousAt u x₀) (hv : ContinuousAt v x₀) (h : u x₀ = v x₀) :
    ∃ r > 0, Metric.ball x₀ r ⊆ s ∧ MapsTo u (Metric.ball x₀ r) (extChartAt I (u x₀)).source ∧
      MapsTo v (Metric.ball x₀ r) (extChartAt I (u x₀)).source := by
  have hu' := hu.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) (u x₀))
  have hv' : v ⁻¹' (extChartAt I (u x₀)).source ∈ 𝓝 x₀ :=
    hv.preimage_mem_nhds (by rw [h]; exact extChartAt_source_mem_nhds (v x₀))
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hs (Filter.inter_mem hu' hv'))
  exact ⟨r, hr, fun x hx ↦ (hrs hx).1, fun x hx ↦ (hrs hx).2.1, fun x hx ↦ (hrs hx).2.2⟩

end TauCeti
