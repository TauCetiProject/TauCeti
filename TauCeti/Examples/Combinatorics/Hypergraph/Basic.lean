/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Hypergraph.Basic

/-!
# Regression examples: finite uniform hypergraphs

These examples exercise uniform hypergraphs and their edge density from a downstream module,
through public statements only:

* on an empty vertex type, an `r`-uniform hypergraph with `r > 0` has no possible edges;
* when `r` exceeds the number of vertices, every density is `0`;
* when `r = 0`, the complete hypergraph has the empty set as its one edge, even on an empty vertex
  type, and has density `1`;
* the complete `2`-uniform hypergraph on two vertices is a single edge, as is the complete
  `3`-uniform hypergraph on three vertices;
* the bridge to Mathlib's `Hypergraph` has the coerced edges.
-/

open Finset TauCeti TauCeti.UniformHypergraph

/-! ### Degenerate hosts and arities -/

-- On an empty vertex type there are no `2`-element edges, so the complete hypergraph is edgeless.
example : #(complete 2 (Fin 0)).edges = 0 := by
  rw [card_edges_complete]
  simp

-- When `r` exceeds the number of vertices, the density is `0`.
example (H : UniformHypergraph 3 (Fin 2)) : H.edgeDensity = 0 :=
  edgeDensity_eq_zero_of_card_lt H (by simp)

-- When `r = 0`, the empty set is an edge of the complete hypergraph, even on an empty vertex type,
-- and the density is `1`.
example : (∅ : Finset (Fin 0)) ∈ (complete 0 (Fin 0)).edges :=
  mem_edges_complete.2 (Finset.card_empty)

example : (complete 0 (Fin 0)).edgeDensity = 1 :=
  edgeDensity_complete (Nat.zero_le _)

-- The empty hypergraph has density `0`.
example : (empty 2 (Fin 5)).edgeDensity = 0 :=
  edgeDensity_empty

/-! ### Small complete hypergraphs -/

-- `K₂`: the complete `2`-uniform hypergraph on two vertices has a single edge and density `1`.
example : #(complete 2 (Fin 2)).edges = 1 := by
  rw [card_edges_complete]
  simp

example : (complete 2 (Fin 2)).edgeDensity = 1 :=
  edgeDensity_complete (by simp)

-- A triangle: the complete `3`-uniform hypergraph on three vertices has a single edge.
example : #(complete 3 (Fin 3)).edges = 1 := by
  rw [card_edges_complete]
  simp

/-! ### The bridge to Mathlib's `Hypergraph` -/

-- The edge of `K₂` is an edge of the Mathlib hypergraph.
example : ((univ : Finset (Fin 2)) : Set (Fin 2)) ∈ (complete 2 (Fin 2)).toHypergraph.edgeSet := by
  rw [coe_mem_toHypergraph_edgeSet, mem_edges_complete]
  simp
