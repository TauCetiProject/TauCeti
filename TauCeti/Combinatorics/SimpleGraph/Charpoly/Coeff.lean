/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import TauCeti.Combinatorics.SimpleGraph.Clique.Basic

/-!
# The first coefficients of the characteristic polynomial of a graph

Write `p_G(t) = det(tI - A)` for the characteristic polynomial of the adjacency matrix `A` of a
finite simple graph `G` on `n` vertices, over a commutative ring, and `a_j` for its coefficient of
`t^(n - j)`. By Mathlib's `Matrix.charpoly_coeff_eq_sum_minors`, `a_j` is `(-1)^j` times the sum
of the principal minors of `A` of order `j`. The principal minors of small order are read off the
graph: those of order `1` vanish, one of order `2` is `-1` on an edge and `0` otherwise, and one of
order `3` is `2` on a triangle and `0` otherwise. Consequently `a₁ = 0`, `a₂ = -m` with `m` the
number of edges, and `a₃ = -2t` with `t` the number of triangles. The first two hold on every
nonempty vertex type and the third for `n ≥ 3`: the index `n - j` is truncated in `ℕ`, and for the
graph `K₂` the coefficient at the truncated index `n - 3 = 0` is `a₂ = -1`, not `-2t = 0`.

The minors are first computed along a family `f : Fin k → V` of vertices, which need not be
injective, and then for the principal submatrix on a set `s` of `k` vertices.

## Main results

* `SimpleGraph.det_submatrix_adjMatrix_fin_two`, `SimpleGraph.det_submatrix_adjMatrix_fin_three`:
  the minors of `A` along a family of two or three vertices.
* `SimpleGraph.det_submatrix_adjMatrix_of_card_eq_one`,
  `SimpleGraph.det_submatrix_adjMatrix_of_card_eq_two`,
  `SimpleGraph.det_submatrix_adjMatrix_of_card_eq_three`: the principal minors of `A` of orders
  `1`, `2` and `3`.
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

/-! ### Minors along a family of vertices -/

/-- The minor of the adjacency matrix along a family of two vertices is `-1` if they are adjacent
and `0` otherwise. -/
theorem det_submatrix_adjMatrix_fin_two (f : Fin 2 → V) :
    ((G.adjMatrix R).submatrix f f).det = if G.Adj (f 0) (f 1) then -1 else 0 := by
  rw [det_fin_two]
  simp only [submatrix_apply, adjMatrix_apply, G.irrefl, ite_false, G.adj_comm (f 1) (f 0)]
  split_ifs <;> simp

/-- The minor of the adjacency matrix along a family of three vertices is `2` if they are
pairwise adjacent and `0` otherwise. -/
theorem det_submatrix_adjMatrix_fin_three (f : Fin 3 → V) :
    ((G.adjMatrix R).submatrix f f).det =
      if G.Adj (f 0) (f 1) ∧ G.Adj (f 0) (f 2) ∧ G.Adj (f 1) (f 2) then 2 else 0 := by
  rw [det_fin_three]
  simp only [submatrix_apply, adjMatrix_apply, G.irrefl, ite_false, G.adj_comm (f 1) (f 0),
    G.adj_comm (f 2) (f 0), G.adj_comm (f 2) (f 1)]
  split_ifs <;> simp_all
  ring

/-! ### Principal minors -/

variable [DecidableEq V]

/-- Enumerating a set `s` of `k` vertices by `Fin k` turns the principal minor on `s` into a minor
along a family of `k` vertices, and the statement that `s` is a clique into the pairwise adjacency
of that family. -/
private theorem exists_det_submatrix_coe_eq {k : ℕ} {s : Finset V} (hs : #s = k) :
    ∃ f : Fin k → V,
      ((G.adjMatrix R).submatrix ((↑) : s → V) (↑)).det = ((G.adjMatrix R).submatrix f f).det ∧
        (G.IsClique (s : Set V) ↔ Pairwise fun i j ↦ G.Adj (f i) (f j)) := by
  let e : Fin k ≃ s := (Fintype.equivFinOfCardEq (by simpa using hs)).symm
  refine ⟨Subtype.val ∘ e, (det_submatrix_equiv_self e _).symm, ?_⟩
  rw [← G.isClique_range_iff_pairwise (Subtype.val_injective.comp e.injective), Set.range_comp,
    e.range_eq_univ, Set.image_univ, Subtype.range_coe]

/-- The principal minors of order `1` of the adjacency matrix vanish. -/
theorem det_submatrix_adjMatrix_of_card_eq_one {s : Finset V} (hs : #s = 1) :
    ((G.adjMatrix R).submatrix ((↑) : s → V) (↑)).det = 0 := by
  obtain ⟨f, hdet, -⟩ := G.exists_det_submatrix_coe_eq (R := R) hs
  simp [hdet]

/-- A principal minor of order `2` of the adjacency matrix is `-1` on an edge and `0` otherwise. -/
theorem det_submatrix_adjMatrix_of_card_eq_two {s : Finset V} (hs : #s = 2) :
    ((G.adjMatrix R).submatrix ((↑) : s → V) (↑)).det =
      if G.IsClique (s : Set V) then -1 else 0 := by
  obtain ⟨f, hdet, hcl⟩ := G.exists_det_submatrix_coe_eq (R := R) hs
  rw [hdet, det_submatrix_adjMatrix_fin_two]
  refine if_congr ?_ rfl rfl
  rw [hcl]
  simp [pairwise_fin_succ_iff, Fin.forall_fin_succ, G.adj_comm (f 1) (f 0)]

/-- A principal minor of order `3` of the adjacency matrix is `2` on a triangle and `0`
otherwise. -/
theorem det_submatrix_adjMatrix_of_card_eq_three {s : Finset V} (hs : #s = 3) :
    ((G.adjMatrix R).submatrix ((↑) : s → V) (↑)).det =
      if G.IsClique (s : Set V) then 2 else 0 := by
  obtain ⟨f, hdet, hcl⟩ := G.exists_det_submatrix_coe_eq (R := R) hs
  rw [hdet, det_submatrix_adjMatrix_fin_three]
  refine if_congr ?_ rfl rfl
  rw [hcl]
  simp [pairwise_fin_succ_iff, Fin.forall_fin_succ, G.adj_comm (f 1) (f 0),
    G.adj_comm (f 2) (f 0), G.adj_comm (f 2) (f 1)]
  tauto

/-! ### The first coefficients -/

variable [Fintype V]

/-- Summing a constant over the `k`-sets of vertices that are cliques counts the `k`-cliques. -/
private theorem sum_powersetCard_ite_isClique (k : ℕ) (c : R) :
    ∑ s ∈ (univ : Finset V).powersetCard k, (if G.IsClique (s : Set V) then c else 0) =
      #(G.cliqueFinset k) • c := by
  rw [← sum_filter, sum_const]
  congr 2
  ext s
  simp [mem_cliqueFinset_iff, isNClique_iff, and_comm]

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
