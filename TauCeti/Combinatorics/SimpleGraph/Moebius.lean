/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import TauCeti.Data.Finset.Basic

/-!
# The Möbius function of the lattice of graphs on a fixed vertex set

The simple graphs on a finite vertex set `V` form a Boolean lattice, isomorphic through the edge
set to the lattice of subsets of the non-diagonal pairs `Sym2 V`.  Its Möbius function is therefore
the signed count `(-1)^{e(H) - e(F)}` on an interval `[F, H]`, where `e(·)` counts edges.  The two
lemmas here are the cancellation laws that drive Möbius inversion over graphs, as in the transform
between a graph parameter and its "contains exactly" coefficients.

## Main results

* `SimpleGraph.sum_neg_one_pow_card_edgeSet_sub_left` — the signed sum
  `∑_{F ≤ G ≤ H} (-1)^{e(G) - e(F)}` is `1` if `F = H` and `0` otherwise;
* `SimpleGraph.sum_neg_one_pow_card_edgeSet_sub_right` — the same for `(-1)^{e(H) - e(G)}`.

Both are transported from `Finset.sum_Icc_neg_one_pow_card_sub_card_left` and
`Finset.sum_Icc_neg_one_pow_card_sub_card_right` along `G ↦ G.edgeFinset`, a bijection from the
graphs between `F` and `H` onto the edge sets between theirs.
-/

public section

namespace SimpleGraph

variable {V R : Type*} [Fintype V] [Ring R]

open Classical in
/-- Summing over the graphs between `F` and `H` is summing over the edge sets between theirs, when
the summand depends on the graph only through its number of edges. -/
private theorem sum_filter_le_le_eq_sum_Icc [DecidableEq V]
    (F H : SimpleGraph V) (φ : ℕ → R) :
    ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph V => F ≤ G ∧ G ≤ H), φ (Nat.card G.edgeSet) =
      ∑ s ∈ Finset.Icc F.edgeFinset H.edgeFinset, φ s.card := by
  -- An edge set below `H.edgeFinset` carries no diagonal pair, so it is the edge set of a graph.
  have hset : ∀ s ∈ Finset.Icc F.edgeFinset H.edgeFinset,
      (fromEdgeSet (s : Set (Sym2 V))).edgeSet = s := fun s hs => by
    rw [edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_left]
    exact fun e he => not_isDiag_of_mem_edgeSet H (mem_edgeFinset.1 ((Finset.mem_Icc.1 hs).2 he))
  refine Finset.sum_nbij' (fun G => G.edgeFinset) (fun s => fromEdgeSet (s : Set (Sym2 V)))
    (fun G hG => ?_) (fun s hs => ?_) (fun G _ => ?_)
    (fun s hs => Finset.coe_injective (by rw [coe_edgeFinset, hset s hs])) (fun G _ => ?_)
  · simpa [edgeFinset_subset_edgeFinset] using hG
  · have hs' := Finset.mem_Icc.1 (Finset.mem_coe.1 hs)
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩) <;>
      rw [← edgeSet_subset_edgeSet, hset s hs, ← coe_edgeFinset, Finset.coe_subset]
    exacts [hs'.1, hs'.2]
  · rw [coe_edgeFinset, fromEdgeSet_edgeSet]
  · rw [Nat.card_eq_fintype_card, edgeFinset_card]

open Classical in
/-- **The Möbius function of the lattice of graphs, measured from the bottom.** The signed sum
`∑_{F ≤ G ≤ H} (-1)^{e(G) - e(F)}` is `1` if `F = H` and `0` otherwise. -/
theorem sum_neg_one_pow_card_edgeSet_sub_left (F H : SimpleGraph V) :
    ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph V => F ≤ G ∧ G ≤ H),
        (-1 : R) ^ (Nat.card G.edgeSet - Nat.card F.edgeSet) = if F = H then 1 else 0 := by
  rw [sum_filter_le_le_eq_sum_Icc F H fun m => (-1 : R) ^ (m - Nat.card F.edgeSet),
    Nat.card_eq_fintype_card, ← edgeFinset_card, Finset.sum_Icc_neg_one_pow_card_sub_card_left]
  exact if_congr edgeFinset_inj rfl rfl

open Classical in
/-- **The Möbius function of the lattice of graphs, measured from the top.** The signed sum
`∑_{F ≤ G ≤ H} (-1)^{e(H) - e(G)}` is `1` if `F = H` and `0` otherwise. -/
theorem sum_neg_one_pow_card_edgeSet_sub_right (F H : SimpleGraph V) :
    ∑ G ∈ Finset.univ.filter (fun G : SimpleGraph V => F ≤ G ∧ G ≤ H),
        (-1 : R) ^ (Nat.card H.edgeSet - Nat.card G.edgeSet) = if F = H then 1 else 0 := by
  rw [sum_filter_le_le_eq_sum_Icc F H fun m => (-1 : R) ^ (Nat.card H.edgeSet - m),
    Nat.card_eq_fintype_card, ← edgeFinset_card, Finset.sum_Icc_neg_one_pow_card_sub_card_right]
  exact if_congr edgeFinset_inj rfl rfl

end SimpleGraph
