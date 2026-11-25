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

A sequence of continuous functions on a compact set is uniformly bounded above as soon as each
point has a neighbourhood on which the functions are eventually bounded above
(`IsCompact.exists_forall_le_of_eventually_nhds`): finitely many such neighbourhoods cover the set,
and each of the finitely many earlier functions is bounded on the compact set.
-/

public section

open Filter Set Topology

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

/-- **Local eventual bounds on a compact set give one bound.** If each `g n` is continuous on the
compact set `C`, and each point of `C` has a neighbourhood on which the `g n` are eventually
bounded above by a common bound, then a single bound holds for all `g n` on all of `C`. -/
theorem IsCompact.exists_forall_le_of_eventually_nhds {X β : Type*} [TopologicalSpace X]
    [LinearOrder β] [TopologicalSpace β] [ClosedIciTopology β] [Nonempty β] {C : Set X}
    (hC : IsCompact C) {g : ℕ → X → β} (hg : ∀ n, ContinuousOn (g n) C)
    (h : ∀ x ∈ C, ∃ U ∈ 𝓝 x, ∃ M, ∀ᶠ n in atTop, ∀ y ∈ U, g n y ≤ M) :
    ∃ M, ∀ n, ∀ y ∈ C, g n y ≤ M := by
  choose! U hU M hM using h
  -- Finitely many of the neighbourhoods `U x` cover `C`, and their bounds hold from some `N` on.
  obtain ⟨T, hTC, hCT⟩ := hC.elim_nhds_subcover U hU
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((eventually_all_finset T).2 fun x hx ↦ hM x (hTC x hx))
  obtain ⟨A, hA⟩ : BddAbove (M '' T) := (T.finite_toSet.image M).bddAbove
  -- Each of the finitely many earlier terms is bounded on `C`.
  obtain ⟨B, hB⟩ : BddAbove (⋃ n ∈ Iio N, g n '' C) :=
    (finite_Iio N).bddAbove_biUnion.2 fun n _ ↦ hC.bddAbove_image (hg n)
  refine ⟨max A B, fun n y hy ↦ ?_⟩
  rcases lt_or_ge n N with hn | hn
  · exact (hB (mem_biUnion hn (mem_image_of_mem _ hy))).trans (le_max_right _ _)
  · obtain ⟨x, hxT, hyx⟩ := mem_iUnion₂.1 (hCT hy)
    exact ((hN n hn x hxT y hyx).trans (hA (mem_image_of_mem _ hxT))).trans (le_max_left _ _)
