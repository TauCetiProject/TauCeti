/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.Compact

/-!
# Boundary extrema on compact sets

A continuous function on a nonempty compact set attains an extremum on the frontier when
interior local extrema are excluded. On a connected noncompact space, transferring every
frontier upper bound to the whole compact set also gives a maximum on the frontier, assuming
continuity there.
-/

public section

open Topology

/-- If every interior point of a compact set is forbidden from being a local maximum, then a
continuous function on the compact set has a maximum point on the frontier. -/
theorem IsCompact.exists_mem_frontier_isMaxOn_of_forall_mem_interior_not_isLocalMax {X β : Type*}
    [TopologicalSpace X] [TopologicalSpace β] [LinearOrder β] [ClosedIciTopology β] {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) {f : X → β} (hcont : ContinuousOn f K)
    (hnot : ∀ ⦃x⦄, x ∈ interior K → ¬ IsLocalMax f x) :
    ∃ x ∈ frontier K, IsMaxOn f K x := by
  obtain ⟨x, hxK, hxmax⟩ := hK.exists_isMaxOn hne hcont
  refine ⟨x, ?_, hxmax⟩
  rw [frontier]
  refine ⟨subset_closure hxK, ?_⟩
  intro hxint
  exact hnot hxint (hxmax.isLocalMax (mem_interior_iff_mem_nhds.mp hxint))

/-- If every interior point of a compact set is forbidden from being a local minimum, then a
continuous function on the compact set has a minimum point on the frontier. -/
theorem IsCompact.exists_mem_frontier_isMinOn_of_forall_mem_interior_not_isLocalMin {X β : Type*}
    [TopologicalSpace X] [TopologicalSpace β] [LinearOrder β] [ClosedIicTopology β] {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) {f : X → β} (hcont : ContinuousOn f K)
    (hnot : ∀ ⦃x⦄, x ∈ interior K → ¬ IsLocalMin f x) :
    ∃ x ∈ frontier K, IsMinOn f K x := by
  obtain ⟨x, hxK, hxmin⟩ := hK.exists_isMinOn hne hcont
  refine ⟨x, ?_, hxmin⟩
  rw [frontier]
  refine ⟨subset_closure hxK, ?_⟩
  intro hxint
  exact hnot hxint (hxmin.isLocalMin (mem_interior_iff_mem_nhds.mp hxint))

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
