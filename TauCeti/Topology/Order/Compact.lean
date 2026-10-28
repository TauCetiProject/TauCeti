/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.Compact

/-!
# Boundary attainment from boundary bounds

On a connected noncompact space, transferring every frontier bound to a nonempty compact set
forces a function continuous on the frontier to attain a maximum there.
-/

public section

open Topology

/-- If a function is continuous on the frontier of a nonempty compact set and every frontier
upper bound also bounds the whole set, then the function attains a maximum on the frontier. -/
theorem IsCompact.exists_mem_frontier_isMaxOn_of_le_frontier {X β : Type*} [TopologicalSpace X]
    [T2Space X] [PreconnectedSpace X] [NoncompactSpace X] [LinearOrder β] [TopologicalSpace β]
    [ClosedIciTopology β] {K : Set X} (hK : IsCompact K) (hne : K.Nonempty) {f : X → β}
    (hcont : ContinuousOn f (frontier K))
    (hbound : ∀ {m : β}, (∀ ⦃x⦄, x ∈ frontier K → f x ≤ m) →
      ∀ ⦃x⦄, x ∈ K → f x ≤ m) :
    ∃ x ∈ frontier K, IsMaxOn f K x := by
  have hfrsub : frontier K ⊆ K := hK.isClosed.frontier_subset
  have hfrcompact : IsCompact (frontier K) := hK.of_isClosed_subset isClosed_frontier hfrsub
  have hfrne : (frontier K).Nonempty :=
    nonempty_frontier_iff.2 ⟨hne, fun h => noncompact_univ X (h ▸ hK)⟩
  obtain ⟨z, hzfr, hzmax⟩ := hfrcompact.exists_isMaxOn hfrne hcont
  exact ⟨z, hzfr, fun y hyK => hbound (fun w hw => hzmax hw) hyK⟩
