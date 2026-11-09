/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Hypergraph.HomDensity
import Mathlib.Tactic.NormNum

/-!
# Regression examples: homomorphism densities of uniform hypergraphs

These examples compute homomorphism densities of small uniform hypergraphs from a downstream
module, through public statements only:

* a single `3`-uniform edge in the complete `3`-uniform hypergraph on four vertices:
  `3! · 4` of the `4³` vertex maps are homomorphisms, while every vertex embedding is one;
* a single `2`-uniform edge, `K₂`, in the complete `2`-uniform hypergraph on three vertices;
* homomorphisms out of a single edge are injective, so a single `3`-uniform edge has `3!`
  homomorphic relabellings to itself and no others;
* the empty host, the empty pattern, and a host with fewer vertices than the pattern;
* the edge density of a simple graph, recovered from its `2`-uniform hypergraph.
-/

open Finset TauCeti TauCeti.UniformHypergraph

/-! ### Single edges in complete hosts -/

-- A single `3`-uniform edge in the complete `3`-uniform hypergraph on four vertices:
-- `3! · 4 = 24` of the `4³ = 64` vertex maps are homomorphisms.
example : (complete 3 (Fin 3)).homDensity (complete 3 (Fin 4)) = 3 / 8 := by
  rw [homDensity_complete_left_of_card_eq (Fintype.card_fin 3), card_edges_complete]
  norm_num [Nat.choose, Nat.factorial]

-- Every vertex embedding of a single `3`-uniform edge is a homomorphism.
example : (complete 3 (Fin 3)).injHomDensity (complete 3 (Fin 4)) = 1 :=
  injHomDensity_complete_right (by simp)

-- The injective density of a single edge is the edge density of the host.
example : (complete 3 (Fin 3)).injHomDensity (complete 3 (Fin 4)) =
    (complete 3 (Fin 4)).edgeDensity :=
  injHomDensity_complete_left_of_card_eq (Fintype.card_fin 3)

-- `K₂` in the complete `2`-uniform hypergraph on three vertices: `2 · 3 = 6` of the `3² = 9`
-- vertex maps are homomorphisms.
example : (complete 2 (Fin 2)).homDensity (complete 2 (Fin 3)) = 2 / 3 := by
  rw [homDensity_complete_left_of_card_eq (Fintype.card_fin 2), card_edges_complete]
  norm_num [Nat.choose, Nat.factorial]

-- The `3!` relabellings of a single `3`-uniform edge are its only homomorphisms to itself: a
-- homomorphism out of a single edge cannot identify two vertices.
example : (complete 3 (Fin 3)).homCount (complete 3 (Fin 3)) = 6 := by
  rw [homCount_complete_left_of_card_eq (Fintype.card_fin 3), card_edges_complete]
  simp [Nat.factorial]

/-! ### Degenerate patterns and hosts -/

-- A pattern with an edge has density `0` in the empty host.
example : (complete 3 (Fin 3)).homDensity (empty 3 (Fin 5)) = 0 :=
  homDensity_empty_right ⟨univ, by simp⟩

-- The empty pattern has density `1` in every nonempty host.
example (H : UniformHypergraph 3 (Fin 5)) : (empty 3 (Fin 7)).homDensity H = 1 :=
  homDensity_empty_left

-- A host with fewer vertices than the pattern has no vertex embeddings, and the injective density
-- is `0`.
example (H : UniformHypergraph 3 (Fin 2)) : (complete 3 (Fin 3)).injHomDensity H = 0 := by
  simp [injHomDensity_def]

/-! ### Simple graphs -/

-- The homomorphism density of `K₂` in a simple graph, computed through its `2`-uniform
-- hypergraph, is twice its number of edges over the square of its number of vertices.
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((⊤ : SimpleGraph (Fin 2)).toUniformHypergraph.homDensity G.toUniformHypergraph : ℝ) =
      2 * #G.edgeFinset / (Fintype.card V ^ 2 : ℝ) := by
  rw [SimpleGraph.homDensity_toUniformHypergraph,
    DenseGraphLimits.homDensityFin_top_fin_two]
