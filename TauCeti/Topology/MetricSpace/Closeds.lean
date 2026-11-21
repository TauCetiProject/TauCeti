/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Closeds

import Mathlib.Topology.MetricSpace.Thickening

/-!
# Separation from and approximation of a Hausdorff limit of closed sets

The type `TopologicalSpace.Closeds X` of closed subsets of a metric space `X` carries the
Hausdorff extended distance (`TopologicalSpace.Closeds.edist_eq`). If closed sets `F i` converge
to `Z` in this distance, then a compact set `K` disjoint from `Z` stays at a uniformly positive
distance from `F i` for all `i` far enough along the filter
(`IsCompact.exists_pos_eventually_le_dist_of_tendsto`). Conversely, every point of `Z` is
eventually arbitrarily close to a point of `F i` (`Filter.Tendsto.eventually_exists_dist_lt`).

This is how Hausdorff convergence of a sequence of zero sets is used: on a compact set away from
the limit, the sets of the sequence eventually keep a fixed distance, so estimates that hold at
a definite distance from the zeros apply uniformly there.
-/

public section

open Filter Metric Set TopologicalSpace Topology

variable {X : Type*} [MetricSpace X]

/-- If closed sets `F i` converge to `Z` in the Hausdorff distance and the compact set `K` is
disjoint from `Z`, there is `δ > 0` such that, eventually, every point of `K` lies at distance at
least `δ` from every point of `F i`. -/
theorem IsCompact.exists_pos_eventually_le_dist_of_tendsto {ι : Type*} {l : Filter ι}
    {K : Set X} (hK : IsCompact K) {F : ι → Closeds X} {Z : Closeds X}
    (hF : Tendsto F l (𝓝 Z)) (hKZ : Disjoint K Z) :
    ∃ δ > 0, ∀ᶠ i in l, ∀ x ∈ K, ∀ y ∈ F i, δ ≤ dist x y := by
  obtain ⟨δ, hδ, hδK⟩ :=
    hK.exists_thickening_subset_open Z.isClosed.isOpen_compl hKZ.subset_compl_right
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  filter_upwards [EMetric.tendsto_nhds.1 hF (ENNReal.ofReal (δ / 2)) (by simpa using hδ)]
    with i hi x hx y hy
  by_contra! hxy
  -- A point `z` of `Z` within `δ / 2` of `y` would lie within `δ` of `x ∈ K`.
  obtain ⟨z, hz, hyz⟩ := exists_edist_lt_of_hausdorffEDist_lt hy hi
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (half_pos hδ)] at hyz
  refine hδK (mem_thickening_iff.2 ⟨x, hx, ?_⟩) hz
  linarith [dist_triangle z y x, dist_comm z y, dist_comm x y]

/-- If closed sets `F i` converge to `Z` in the Hausdorff distance, then every point of `Z` is
eventually within any prescribed positive distance of a point of `F i`. -/
theorem Filter.Tendsto.eventually_exists_dist_lt {ι : Type*} {l : Filter ι}
    {F : ι → Closeds X} {Z : Closeds X} (hF : Tendsto F l (𝓝 Z)) {x : X} (hx : x ∈ Z) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ i in l, ∃ y ∈ F i, dist x y < ε := by
  filter_upwards [EMetric.tendsto_nhds.1 hF (ENNReal.ofReal ε) (by simpa using hε)] with i hi
  rw [edist_comm, Closeds.edist_eq] at hi
  obtain ⟨y, hy, hxy⟩ := exists_edist_lt_of_hausdorffEDist_lt hx hi
  exact ⟨y, hy, by rwa [edist_dist, ENNReal.ofReal_lt_ofReal_iff hε] at hxy⟩
