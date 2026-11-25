/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Basic lemmas for simple graphs

This file supplements `Mathlib.Combinatorics.SimpleGraph.Basic` with round-trip identities for
`SimpleGraph.fromRel` and characterizations of adjacency and edge sets for the symmetric difference
`G₁ ∆ G₂` of two simple graphs.

## Main results

* `SimpleGraph.fromRel_adj_self` and `SimpleGraph.fromRel_ite_ne_one`: recovering a simple graph
  from its own adjacency relation or from a `{1, t}` edge indicator (`t ≠ 1`) via
  `SimpleGraph.fromRel`.
* `SimpleGraph.symmDiff_adj` and `SimpleGraph.edgeSet_symmDiff`: adjacency in `G₁ ∆ G₂` is given by
  `Xor`, and `(G₁ ∆ G₂).edgeSet = G₁.edgeSet ∆ G₂.edgeSet`.
-/

public section

open scoped symmDiff

namespace SimpleGraph

variable {V : Type*}

/-- Constructing a simple graph via `SimpleGraph.fromRel` from its own adjacency relation recovers
the graph. -/
@[simp]
theorem fromRel_adj_self (G : SimpleGraph V) : fromRel G.Adj = G := by
  ext u v
  exact ⟨fun ⟨_, h⟩ => h.elim id (G.adj_comm v u).mp, fun h => ⟨G.ne_of_adj h, Or.inl h⟩⟩

/-- Recovering a simple graph from its `{1, t}` edge indicator (`t ≠ 1`) returns the original
graph. -/
theorem fromRel_ite_ne_one {M : Type*} [One M] (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : M} (ht : t ≠ 1) :
    fromRel (fun u v => (if G.Adj u v then t else 1) ≠ 1) = G := by
  simp [ht]

/-- Two vertices are adjacent in `G₁ ∆ G₂` if and only if they are adjacent in exactly one of `G₁`
and `G₂`. -/
@[simp]
theorem symmDiff_adj (G₁ G₂ : SimpleGraph V) (u v : V) :
    (G₁ ∆ G₂).Adj u v ↔ Xor (G₁.Adj u v) (G₂.Adj u v) := by
  simp only [symmDiff_def, sup_adj, sdiff_adj, Xor]

/-- The edge set of `G₁ ∆ G₂` is the symmetric difference of their edge sets. -/
@[simp]
theorem edgeSet_symmDiff (G₁ G₂ : SimpleGraph V) :
    (G₁ ∆ G₂).edgeSet = G₁.edgeSet ∆ G₂.edgeSet := by
  simp only [symmDiff_def, edgeSet_sup, edgeSet_sdiff]

end SimpleGraph
