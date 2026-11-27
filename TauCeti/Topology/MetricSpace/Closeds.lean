/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Closeds
public import TauCeti.Topology.Sets.KuratowskiLimit

import Mathlib.Topology.MetricSpace.Thickening

/-!
# Hausdorff and Kuratowski limits of closed sets in a metric space

The type `TopologicalSpace.Closeds X` of closed subsets of an extended metric space `X` carries the
Hausdorff extended distance (`TopologicalSpace.Closeds.edist_eq`). This file compares convergence
in this distance with the local notion of Kuratowski convergence, `TauCeti.IsKuratowskiLimit`.

* If closed sets `F i` converge to `Z` in the Hausdorff distance, then `F i` converges to `Z` in
  the sense of Kuratowski (`Filter.Tendsto.isKuratowskiLimit`). For Kuratowski limits in a
  pseudometric space, every point of `Z` is eventually arbitrarily close to a point of `F i`
  (`TauCeti.IsKuratowskiLimit.eventually_exists_dist_lt`).
* When `X` is compact the converse holds, so the two notions of convergence of closed sets agree
  (`TauCeti.isKuratowskiLimit_iff_tendsto`). On a noncompact space Kuratowski convergence is
  weaker: the sets `{n}` of `ℝ` converge to `∅` in the sense of Kuratowski but stay at Hausdorff
  distance `∞` from it.
* A compact set `K` disjoint from a Kuratowski limit stays at a uniformly positive distance from
  the sets for all indices far enough along the filter
  (`IsCompact.exists_pos_eventually_le_dist_of_isKuratowskiLimit`).

This is how convergence of a sequence of zero sets is used: on a compact set away from the limit,
the sets of the sequence eventually keep a fixed distance, so estimates that hold at a definite
distance from the zeros apply uniformly there.

The extended distance on `TopologicalSpace.NonemptyCompacts X` is likewise the Hausdorff extended
distance (`TopologicalSpace.NonemptyCompacts.edist_eq`).
-/

public section

open Filter Metric Set TopologicalSpace Topology

variable {ι : Type*} {l : Filter ι}

section EMetricSpace

variable {X : Type*} [EMetricSpace X]

/-- **Hausdorff convergence implies Kuratowski convergence.** If closed sets `F i` converge to `Z`
in the Hausdorff distance, they converge to `Z` in the sense of Kuratowski. -/
theorem Filter.Tendsto.isKuratowskiLimit {F : ι → Closeds X} {Z : Closeds X}
    (hF : Tendsto F l (𝓝 Z)) : TauCeti.IsKuratowskiLimit l (fun i ↦ (F i : Set X)) Z where
  eventually_inter_nonempty x hx U hU := by
    obtain ⟨ε, hε, hεU⟩ := EMetric.mem_nhds_iff.1 hU
    filter_upwards [EMetric.tendsto_nhds.1 hF ε hε] with i hi
    rw [edist_comm, Closeds.edist_eq] at hi
    obtain ⟨y, hy, hxy⟩ := exists_edist_lt_of_hausdorffEDist_lt hx hi
    exact ⟨y, hy, hεU (mem_eball'.2 hxy)⟩
  exists_mem_nhds_eventually_disjoint x hx := by
    obtain ⟨ε, hε, hεZ⟩ := EMetric.mem_nhds_iff.1 (Z.isClosed.isOpen_compl.mem_nhds hx)
    have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
    refine ⟨eball x (ε / 2), eball_mem_nhds x hε2, ?_⟩
    filter_upwards [EMetric.tendsto_nhds.1 hF (ε / 2) hε2] with i hi
    rw [Closeds.edist_eq] at hi
    refine Set.disjoint_left.2 fun y hy hyx ↦ ?_
    -- A point `z` of `Z` within `ε / 2` of `y ∈ ball x (ε / 2)` would lie in `ball x ε ⊆ Zᶜ`.
    obtain ⟨z, hz, hyz⟩ := exists_edist_lt_of_hausdorffEDist_lt hy hi
    refine hεZ (mem_eball.2 ?_) hz
    exact (edist_triangle_left z x y).trans_lt <|
      (ENNReal.add_lt_add hyz (mem_eball.1 hyx)).trans_eq (ENNReal.add_halves ε)

/-- **Kuratowski and Hausdorff convergence agree on a compact space.** In a compact extended
metric space, closed sets `F i` converge to `Z` in the sense of Kuratowski exactly when they
converge to `Z` in the Hausdorff distance. -/
theorem TauCeti.isKuratowskiLimit_iff_tendsto [CompactSpace X] {F : ι → Closeds X}
    {Z : Closeds X} : IsKuratowskiLimit l (fun i ↦ (F i : Set X)) Z ↔ Tendsto F l (𝓝 Z) := by
  refine ⟨fun h ↦ tendsto_nhds_of_unique_mapClusterPt fun Z' hZ' ↦ ?_,
    Filter.Tendsto.isKuratowskiLimit⟩
  -- Along an ultrafilter finer than `l` on which `F` tends to the cluster point `Z'`, both `Z'` and
  -- `Z` are Kuratowski limits of `F`, so they coincide.
  obtain ⟨U, hUl, hU⟩ := mapClusterPt_iff_ultrafilter.1 hZ'
  exact Closeds.ext <| hU.isKuratowskiLimit.unique (h.comp (tendsto_id'.2 hUl))

end EMetricSpace

/-- If the sets `F i` converge to `Z` in the sense of Kuratowski, then every point of `Z` is
eventually within any prescribed positive distance of a point of `F i`. -/
theorem TauCeti.IsKuratowskiLimit.eventually_exists_dist_lt {Y : Type*} [PseudoMetricSpace Y]
    {F : ι → Set Y} {Z : Set Y} (hF : TauCeti.IsKuratowskiLimit l F Z) {x : Y} (hx : x ∈ Z)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ i in l, ∃ y ∈ F i, dist y x < ε :=
  (hF.eventually_inter_nonempty x hx _ (ball_mem_nhds x hε)).mono fun _ ⟨y, hy, hyx⟩ ↦
    ⟨y, hy, mem_ball.1 hyx⟩

/-- **Compact separation from a Kuratowski limit in a metric space.** If the sets `F i` converge to
`Z` in the sense of Kuratowski and the compact set `K` is disjoint from `Z`, there is `δ > 0` such
that, eventually, every point of `K` lies at distance at least `δ` from every point of `F i`. -/
theorem IsCompact.exists_pos_eventually_le_dist_of_isKuratowskiLimit {Y : Type*}
    [PseudoMetricSpace Y] {K : Set Y} (hK : IsCompact K) {F : ι → Set Y} {Z : Set Y}
    (hF : TauCeti.IsKuratowskiLimit l F Z)
    (hKZ : Disjoint K Z) : ∃ δ > 0, ∀ᶠ i in l, ∀ x ∈ K, ∀ y ∈ F i, δ ≤ dist x y := by
  obtain ⟨U, hU, hFU⟩ := hF.exists_mem_nhdsSet_eventually_disjoint hK hKZ
  obtain ⟨V, hV, hKV, hVU⟩ := mem_nhdsSet_iff_exists.1 hU
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_thickening_subset_open hV hKV
  refine ⟨δ, hδ, hFU.mono fun i hi x hx y hy ↦ ?_⟩
  by_contra! hxy
  exact Set.disjoint_left.1 hi hy (hVU (hδK (mem_thickening_iff.2 ⟨x, hx, by rwa [dist_comm]⟩)))

namespace TopologicalSpace.NonemptyCompacts

/-- The extended distance on `NonemptyCompacts α` is the Hausdorff extended distance, by
construction of its emetric space instance. -/
theorem edist_eq {α : Type*} [EMetricSpace α] {s t : NonemptyCompacts α} :
    edist s t = hausdorffEDist (s : Set α) t :=
  rfl

end TopologicalSpace.NonemptyCompacts
