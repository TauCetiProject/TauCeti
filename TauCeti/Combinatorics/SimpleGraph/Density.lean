/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Density

/-!
# Edge counts between finsets of vertices

Two facts about Mathlib's `SimpleGraph.interedges` and `SimpleGraph.edgeDensity` used when
comparing edge densities across a refinement of vertex partitions: the edge count between two
finsets is their size product times their edge density (with no nonemptiness hypothesis, since
both sides vanish on an empty finset), and edge counts are additive over disjoint unions on
either side.
-/

public section

open Finset

namespace SimpleGraph

variable {V ι : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of edges between two finsets is their size product times their edge density. This
holds without nonemptiness hypotheses: if either finset is empty, both sides vanish. -/
theorem card_mul_card_mul_edgeDensity (s t : Finset V) :
    (#s * #t : ℚ) * G.edgeDensity s t = #(G.interedges s t) := by
  rcases eq_or_ne ((#s : ℚ) * #t) 0 with hst | hst
  · have h0 : #s * #t = 0 := by exact_mod_cast hst
    rw [hst, zero_mul, eq_comm, Nat.cast_eq_zero]
    exact Nat.le_zero.1 (h0 ▸ G.card_interedges_le_mul s t)
  · rw [edgeDensity_def, mul_div_cancel₀ _ hst]

variable [DecidableEq V]

/-- Edge counts are additive over a pairwise disjoint union on the left. -/
theorem card_interedges_biUnion_left (s : Finset ι) (t : Finset V) (f : ι → Finset V)
    (hf : (s : Set ι).PairwiseDisjoint f) :
    #(G.interedges (s.biUnion f) t) = ∑ i ∈ s, #(G.interedges (f i) t) := by
  rw [interedges_biUnion_left, card_biUnion]
  exact fun i hi j hj hij => G.interedges_disjoint_left (hf hi hj hij) t

/-- Edge counts are additive over a pairwise disjoint union on the right. -/
theorem card_interedges_biUnion_right (s : Finset V) (t : Finset ι) (f : ι → Finset V)
    (hf : (t : Set ι).PairwiseDisjoint f) :
    #(G.interedges s (t.biUnion f)) = ∑ i ∈ t, #(G.interedges s (f i)) := by
  rw [interedges_biUnion_right, card_biUnion]
  exact fun i hi j hj hij => G.interedges_disjoint_right s (hf hi hj hij)

end SimpleGraph
