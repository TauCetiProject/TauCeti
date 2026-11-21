/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.GDelta.Basic

/-!
# The interior of a dense constructible set

A constructible set has nowhere dense frontier. Consequently, a dense constructible set
has dense interior. This supplies the open subset of a dominant finite-presentation image
used in conjunction with Chevalley's theorem.
-/

public section

namespace Topology.IsConstructible

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- The frontier of a constructible set is nowhere dense. -/
theorem isNowhereDense_frontier (hs : IsConstructible s) : IsNowhereDense (frontier s) := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    rw [isClosed_frontier.isNowhereDense_iff, ← frontier_compl]
    exact interior_frontier hU.isClosed_compl
  | union s _ t _ hs ht =>
    exact (hs.union ht).mono <| (frontier_union_subset s t).trans <|
      Set.union_subset_union Set.inter_subset_left Set.inter_subset_right
  | compl s _ hs => rwa [frontier_compl]

/-- A dense constructible set has dense interior, with no separation hypothesis. -/
theorem dense_interior (hs : IsConstructible s) (hd : Dense s) : Dense (interior s) := by
  have h : Dense (frontier s)ᶜ :=
    (isClosed_isNowhereDense_iff_compl.mp ⟨isClosed_frontier, hs.isNowhereDense_frontier⟩).2
  rwa [← closure_sdiff_frontier, hd.closure_eq, ← Set.compl_eq_univ_sdiff]

end Topology.IsConstructible
