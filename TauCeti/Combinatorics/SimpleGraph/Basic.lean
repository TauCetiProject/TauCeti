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
* `SimpleGraph.symmDiff_adj`, `SimpleGraph.edgeSet_symmDiff`, `SimpleGraph.SymmDiff.adjDecidable`,
  and `SimpleGraph.xor_symmDiff_adj`: adjacency, decidable adjacency, edge set, and triple
  edge-parity in `G₁ ∆ G₂`.
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

/-- Adjacency in a symmetric difference of graphs with decidable adjacency is decidable. -/
instance SymmDiff.adjDecidable (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G ∆ H).Adj :=
  inferInstanceAs <| DecidableRel fun u v ↦ Xor (G.Adj u v) (H.Adj u v)

/-- The edge set of `G₁ ∆ G₂` is the symmetric difference of their edge sets. -/
@[simp]
theorem edgeSet_symmDiff (G₁ G₂ : SimpleGraph V) :
    (G₁ ∆ G₂).edgeSet = G₁.edgeSet ∆ G₂.edgeSet := by
  simp only [symmDiff_def, edgeSet_sup, edgeSet_sdiff]

/-- Around any three vertices `u`, `v`, `w`, the parity of adjacent pairs among `(u, v)`, `(v, w)`,
and `(w, u)` in `G₁ ∆ G₂` is the `Xor` of those parities in `G₁` and `G₂`. -/
theorem xor_symmDiff_adj (G₁ G₂ : SimpleGraph V) (u v w : V) :
    Xor ((G₁ ∆ G₂).Adj u v) (Xor ((G₁ ∆ G₂).Adj v w) ((G₁ ∆ G₂).Adj w u)) ↔
      Xor (Xor (G₁.Adj u v) (Xor (G₁.Adj v w) (G₁.Adj w u)))
        (Xor (G₂.Adj u v) (Xor (G₂.Adj v w) (G₂.Adj w u))) := by
  simp only [symmDiff_adj]
  grind

end SimpleGraph
