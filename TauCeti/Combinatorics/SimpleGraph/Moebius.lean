/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card
public import TauCeti.Data.Finset.Basic

/-!
# The Möbius function of the lattice of graphs on a fixed vertex set

The simple graphs on a finite vertex set `V` form a Boolean lattice, isomorphic through the edge
set to the lattice of subsets of the non-diagonal pairs `Sym2 V`.  Its Möbius function is therefore
the signed count `(-1)^{e(H) - e(F)}` on an interval `[F, H]`, where `e(·)` counts edges.  The two
lemmas here are the cancellation laws that drive Möbius inversion over graphs, as in the transform
between a graph parameter and its "contains exactly" coefficients.

## Main results

* `SimpleGraph.sum_neg_one_pow_ncard_edgeSet_sub_left` — the signed sum
  `∑_{F ≤ G ≤ H} (-1)^{e(G) - e(F)}` is `1` if `F = H` and `0` otherwise;
* `SimpleGraph.sum_neg_one_pow_ncard_edgeSet_sub_right` — the same for `(-1)^{e(H) - e(G)}`.

They are the graph counterparts of `Finset.sum_Icc_neg_one_pow_card_sub_card_left` and
`Finset.sum_Icc_neg_one_pow_card_sub_card_right`: `G ↦ G.edgeFinset` maps the graphs between `F`
and `H` bijectively onto the edge sets between theirs.
-/

public section

open Finset

namespace SimpleGraph

variable {V R : Type*} [Fintype V] [DecidableEq V] [Ring R]

/-- Summing over the graphs between `F` and `H` a function of their edge sets is summing it over the
edge sets between theirs. -/
private theorem sum_filter_le_le_eq_sum_Icc_edgeFinset {M : Type*} [AddCommMonoid M]
    (F H : SimpleGraph V) [DecidablePred fun G : SimpleGraph V => F ≤ G ∧ G ≤ H]
    [∀ G : SimpleGraph V, Fintype G.edgeSet] (f : Finset (Sym2 V) → M) :
    ∑ G with F ≤ G ∧ G ≤ H, f G.edgeFinset = ∑ s ∈ Icc F.edgeFinset H.edgeFinset, f s := by
  -- An edge set below `H.edgeFinset` carries no diagonal pair, so it is the edge set of a graph.
  have hset : ∀ s ∈ Icc F.edgeFinset H.edgeFinset,
      (fromEdgeSet (s : Set (Sym2 V))).edgeFinset = s := fun s hs => coe_injective <| by
    rw [coe_edgeFinset, edgeSet_fromEdgeSet, sdiff_eq_left, Set.disjoint_left]
    exact fun e he => not_isDiag_of_mem_edgeSet H (mem_edgeFinset.1 ((mem_Icc.1 hs).2 he))
  refine sum_nbij' (fun G => G.edgeFinset) (fun s => fromEdgeSet (s : Set (Sym2 V)))
    (fun G hG => ?_) (fun s hs => ?_) (fun G _ => ?_) hset (fun G _ => rfl)
  · simpa [edgeFinset_subset_edgeFinset] using hG
  · refine mem_coe.2 ((mem_filter_univ _).2 ?_)
    rw [← edgeFinset_subset_edgeFinset, ← edgeFinset_subset_edgeFinset, hset s hs]
    exact mem_Icc.1 hs
  · rw [coe_edgeFinset, fromEdgeSet_edgeSet]

/-- **The Möbius function of the lattice of graphs, measured from the bottom.** The signed sum
`∑_{F ≤ G ≤ H} (-1)^{e(G) - e(F)}` is `1` if `F = H` and `0` otherwise. -/
@[simp]
theorem sum_neg_one_pow_ncard_edgeSet_sub_left (F H : SimpleGraph V)
    [DecidablePred fun G : SimpleGraph V => F ≤ G ∧ G ≤ H] [Decidable (F = H)] :
    ∑ G with F ≤ G ∧ G ≤ H, (-1 : R) ^ (G.edgeSet.ncard - F.edgeSet.ncard) =
      if F = H then 1 else 0 := by
  classical
  simp only [← coe_edgeFinset, Set.ncard_coe_finset]
  rw [sum_filter_le_le_eq_sum_Icc_edgeFinset F H fun s => (-1 : R) ^ (#s - #F.edgeFinset),
    sum_Icc_neg_one_pow_card_sub_card_left]
  exact if_congr edgeFinset_inj rfl rfl

/-- **The Möbius function of the lattice of graphs, measured from the top.** The signed sum
`∑_{F ≤ G ≤ H} (-1)^{e(H) - e(G)}` is `1` if `F = H` and `0` otherwise. -/
@[simp]
theorem sum_neg_one_pow_ncard_edgeSet_sub_right (F H : SimpleGraph V)
    [DecidablePred fun G : SimpleGraph V => F ≤ G ∧ G ≤ H] [Decidable (F = H)] :
    ∑ G with F ≤ G ∧ G ≤ H, (-1 : R) ^ (H.edgeSet.ncard - G.edgeSet.ncard) =
      if F = H then 1 else 0 := by
  classical
  simp only [← coe_edgeFinset, Set.ncard_coe_finset]
  rw [sum_filter_le_le_eq_sum_Icc_edgeFinset F H fun s => (-1 : R) ^ (#H.edgeFinset - #s),
    sum_Icc_neg_one_pow_card_sub_card_right]
  exact if_congr edgeFinset_inj rfl rfl

end SimpleGraph
