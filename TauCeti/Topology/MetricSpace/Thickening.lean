/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening

import Mathlib.Topology.Order.DenselyOrdered

/-!
# Pairwise disjoint thickenings

Compact pairwise disjoint sets in a finite family in an extended metric space admit pairwise
disjoint thickenings of one common positive radius. This supplies uniformly separated
neighborhoods, for example the component neighborhoods used to construct disjoint solid-torus
neighborhoods of a link.
-/

public section

open Set Metric Function
open scoped Topology

namespace TauCeti

/-- A finite family of pairwise disjoint compact sets in an extended metric space admits pairwise
disjoint thickenings of one common positive radius. This extends Mathlib's two-set result
`Disjoint.exists_thickenings`. -/
theorem exists_thickenings_pairwiseDisjoint
    {X ι : Type*} [EMetricSpace X] [Finite ι]
    (K : ι → Set X) (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise (Disjoint on K)) :
    ∃ δ : ℝ, 0 < δ ∧ Pairwise (Disjoint on fun i => thickening δ (K i)) := by
  have h : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      Pairwise (Disjoint on fun i => thickening δ (K i)) := by
    simp only [Pairwise, Filter.eventually_all]
    intro i j hij
    obtain ⟨δ, hδ, hd⟩ := (hdisj hij).exists_thickenings (hK i) (hK j).isClosed
    filter_upwards [eventually_lt_nhds hδ |>.filter_mono nhdsWithin_le_nhds] with ε hε
    exact hd.mono (thickening_mono hε.le _) (thickening_mono hε.le _)
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  exact (hpos.and h).exists

end TauCeti
