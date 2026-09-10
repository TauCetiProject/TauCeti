/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Reconstructing a finite graph from its edges

`SimpleGraph.fromEdgeSet` and `SimpleGraph.edgeFinset` are inverse to one another on finite sets
of loop-free edges: rebuilding a graph from such a set returns a graph with exactly those edges.
This is what makes a finite set of edges a faithful parameter for a graph, so that a family of
graphs can be reindexed by the sets of edges it is allowed to use.

## Main results

* `SimpleGraph.edgeFinset_fromEdgeSet_eq_of_subset_top` — a finite set of loop-free edges is the
  edge finset of the graph it generates.
-/

public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge finset of a graph rebuilt from a loop-free finite edge set is the original set.
Loop-freeness is expressed as containment in the edges of the complete graph. -/
theorem edgeFinset_fromEdgeSet_eq_of_subset_top (S : Finset (Sym2 V))
    (hS : S ⊆ (⊤ : SimpleGraph V).edgeFinset) :
    (fromEdgeSet (↑S : Set (Sym2 V))).edgeFinset = S := by
  ext e
  simp only [mem_edgeFinset, edgeSet_fromEdgeSet, Set.mem_sdiff, Finset.mem_coe,
    Sym2.mem_diagSet]
  exact ⟨fun h => h.1, fun h => ⟨h, fun hdiag =>
    (⊤ : SimpleGraph V).not_isDiag_of_mem_edgeSet (mem_edgeFinset.mp (hS h)) hdiag⟩⟩

end SimpleGraph
