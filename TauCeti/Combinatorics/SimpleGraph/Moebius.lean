/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Finite
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
`Finset.sum_Icc_neg_one_pow_card_sub_card_right`, to which
`SimpleGraph.sum_filter_le_le_eq_sum_Icc_edgeFinset` identifies them.
-/

public section

open Finset

namespace SimpleGraph

variable {V R : Type*} [Fintype V] [DecidableEq V] [Ring R]

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
