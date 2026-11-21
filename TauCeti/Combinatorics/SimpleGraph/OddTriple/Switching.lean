/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Bipartite
public import TauCeti.Combinatorics.SimpleGraph.OddTriple.Basic

/-!
# Cut-switching invariance for odd triples

Switching a finite graph `G` by a complete-graph cut `(⊤ : SimpleGraph V).between S Sᶜ` preserves
the parity of adjacent pairs in every vertex triple, and hence leaves `G.oddTripleFinset`
unchanged (`SimpleGraph.oddTripleFinset_symmDiff_top_between`).
-/

public section

open Finset
open scoped symmDiff

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Switching a finite graph by a complete-graph cut preserves `oddTripleFinset`. -/
@[simp]
theorem oddTripleFinset_symmDiff_top_between (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) [DecidablePred (· ∈ S)] :
    (G ∆ (⊤ : SimpleGraph V).between S Sᶜ).oddTripleFinset = G.oddTripleFinset := by
  ext s
  by_cases hs : #s = 3
  · obtain ⟨a, b, c, -, -, -, rfl⟩ := card_eq_three.mp hs
    simp only [triple_mem_oddTripleFinset_iff]
    rw [(G ∆ _).adj_comm a c, G.adj_comm a c, xor_comm ((G ∆ _).Adj c a), xor_comm (G.Adj c a)]
    exact G.xor_symmDiff_top_between_compl_adj S a b c
  · simp [mem_oddTripleFinset, hs]

end SimpleGraph
