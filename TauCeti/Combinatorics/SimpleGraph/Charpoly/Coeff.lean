/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import TauCeti.Combinatorics.SimpleGraph.AdjMatrix
import TauCeti.Combinatorics.SimpleGraph.Clique.Basic

/-!
# The first coefficients of the characteristic polynomial of a graph

Write `p_G(t) = det(tI - A)` for the characteristic polynomial of the adjacency matrix `A` of a
finite simple graph `G` on `n` vertices, over a commutative ring, and `a_j` for its coefficient of
`t^(n - j)`. By Mathlib's `Matrix.charpoly_coeff_eq_sum_minors`, for `j ≤ n` the coefficient `a_j`
is `(-1)^j` times the sum of the principal minors of `A` of order `j`. The principal minors of small
order are read off the graph: those of order `1` vanish, one of order `2` is `-1` on an edge and `0`
otherwise, and one of order `3` is `2` on a triangle and `0` otherwise. Consequently `a₁ = 0`,
`a₂ = -m` with `m` the number of edges, and `a₃ = -2t` with `t` the number of triangles. The first
two hold on every nonempty vertex type and the third for `n ≥ 3`: the index `n - j` is truncated in
`ℕ`, and for the graph `K₂` the coefficient at the truncated index `n - 3 = 0` is `a₂ = -1`, not
`-2t = 0`.

The small principal minors are computed in `TauCeti.Combinatorics.SimpleGraph.AdjMatrix`.

## Main results

* `SimpleGraph.coeff_charpoly_adjMatrix_card_sub_one`,
  `SimpleGraph.coeff_charpoly_adjMatrix_card_sub_two`,
  `SimpleGraph.coeff_charpoly_adjMatrix_card_sub_three`: `a₁ = 0`, `a₂ = -m` and `a₃ = -2t`.

## References

* N. Biggs, *Algebraic Graph Theory*, 2nd ed., Cambridge University Press, 1993,
  Proposition 2.3, p. 8.
-/

public section

open Finset Matrix

namespace SimpleGraph

variable {V R : Type*} (G : SimpleGraph V) [DecidableRel G.Adj] [CommRing R]

/-! ### The first coefficients -/

variable [DecidableEq V] [Fintype V]

/-- The coefficient of `t^(n - 1)` in the characteristic polynomial of a graph on a nonempty
vertex type vanishes. -/
theorem coeff_charpoly_adjMatrix_card_sub_one [Nonempty V] :
    (G.adjMatrix R).charpoly.coeff (Fintype.card V - 1) = 0 := by
  rw [← neg_eq_zero, ← trace_eq_neg_charpoly_coeff, trace_adjMatrix]

/-- The coefficient of `t^(n - 2)` in the characteristic polynomial of a graph on a nonempty
vertex type is minus its number of edges. For `n = 1` the index `n - 2` is truncated to `0`, and
both sides vanish. -/
theorem coeff_charpoly_adjMatrix_card_sub_two [Nonempty V] :
    (G.adjMatrix R).charpoly.coeff (Fintype.card V - 2) = -#G.edgeFinset := by
  obtain hn | hn := le_or_gt 2 (Fintype.card V)
  · rw [charpoly_coeff_eq_sum_minors _ _ hn,
      sum_congr rfl fun s hs ↦ G.det_submatrix_adjMatrix_of_card_eq_two (mem_powersetCard.1 hs).2,
      sum_powersetCard_ite_isClique, card_cliqueFinset_two]
    simp
  -- On a single vertex there is no edge and the adjacency matrix vanishes.
  have h1 : Fintype.card V = 1 := by
    have := Fintype.card_pos (α := V)
    omega
  have hA : G.adjMatrix R = 0 := by
    ext u v
    simp [Fintype.card_le_one_iff.1 h1.le u v]
  have hm : #G.edgeFinset = 0 := by
    simpa [h1] using G.card_edgeFinset_le_card_choose_two
  simp [hA, hm, h1, charpoly_zero]

/-- For `n ≥ 3`, the coefficient of `t^(n - 3)` in the characteristic polynomial of a graph is
minus twice its number of triangles. -/
theorem coeff_charpoly_adjMatrix_card_sub_three (hn : 3 ≤ Fintype.card V) :
    (G.adjMatrix R).charpoly.coeff (Fintype.card V - 3) = -2 * #(G.cliqueFinset 3) := by
  rw [charpoly_coeff_eq_sum_minors _ _ hn,
    sum_congr rfl fun s hs ↦ G.det_submatrix_adjMatrix_of_card_eq_three (mem_powersetCard.1 hs).2,
    sum_powersetCard_ite_isClique]
  simp [nsmul_eq_mul]
  ring

end SimpleGraph
