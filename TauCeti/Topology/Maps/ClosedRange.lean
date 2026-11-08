/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ClusterPt

/-!
# Closed ranges from convergence

A map has closed range if every limit of its values along a nontrivial filter on its
source belongs to its range. This criterion allows reconstruction theorems for limits to
supply closed-image statements without repeating the closure argument.
-/

public section

open Set Filter Topology

namespace TauCeti

/-- A map has closed range if every limit along a nontrivial source filter is in its range.
No topology on the source or separation assumption on the target is required. -/
theorem isClosed_range_of_tendsto {α β : Type*} [TopologicalSpace β] {j : α → β}
    (h : ∀ (g : β) (l : Filter α) [l.NeBot], Tendsto j l (𝓝 g) → g ∈ range j) :
    IsClosed (range j) := by
  refine isClosed_of_closure_subset fun g hg ↦ ?_
  have : (comap j (𝓝 g)).NeBot := by
    rw [comap_neBot_iff]
    intro s hs
    obtain ⟨z, hz⟩ := mem_closure_iff_nhds'.mp hg s hs
    obtain ⟨x, hx⟩ := z.property
    exact ⟨x, hx.symm ▸ hz⟩
  exact h g _ tendsto_comap

end TauCeti
