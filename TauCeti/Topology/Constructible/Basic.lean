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
    rw [IsNowhereDense, isClosed_frontier.closure_eq, ← frontier_compl]
    exact interior_frontier hU.isClosed_compl
  | union s _ t _ hs ht =>
    apply (hs.union ht).mono
    exact (frontier_union_subset s t).trans (by intro x hx; grind)
  | compl s _ hs => simpa only [frontier_compl] using hs

/-- A dense constructible set has dense interior, with no separation hypothesis. -/
theorem dense_interior (hs : IsConstructible s) (hd : Dense s) : Dense (interior s) := by
  have h := (isClosed_isNowhereDense_iff_compl.mp
    ⟨isClosed_frontier, hs.isNowhereDense_frontier⟩).2
  have hi : (frontier s)ᶜ = interior s := by
    simpa [hd.closure_eq, Set.sdiff_eq] using closure_sdiff_frontier s
  exact hi ▸ h

end Topology.IsConstructible
