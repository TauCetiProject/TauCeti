/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import TauCeti.Combinatorics.SimpleGraph.Clique.Basic
import TauCeti.Combinatorics.SimpleGraph.Finite

/-!
# The adjacency, degree and Laplacian matrices

The adjacency matrix `G.adjMatrix R` and the degree matrix `G.degMatrix R` of a simple graph have
entries built from `0`, `1` and natural-number casts, so applying a coefficient map entrywise
gives the same matrix over the target ring. The entries of the square of the adjacency matrix
count common neighbours.

The minors of the adjacency matrix of small order are read off the graph: along a family
`f : Fin k → V` of vertices, which need not be injective, the minor of order `2` is `-1` if the
two vertices are adjacent and `0` otherwise, and that of order `3` is `2` if the three vertices
are pairwise adjacent and `0` otherwise. Hence the principal minors of order `1` vanish, a
principal minor of order `2` is `-1` on an edge and `0` otherwise, and one of order `3` is `2` on
a triangle and `0` otherwise. They give the first coefficients of the characteristic polynomial.

The adjacency, degree and Laplacian matrices are additive over the union `G ⊔ H` of two
edge-disjoint graphs on one vertex type. Consequently, for `G ≤ H` the Laplacian of the graph
`H \ G` of the edges of `H` not in `G` is the difference `L(H) - L(G)`; comparisons of Laplacian
spectra under adding edges rest on this decomposition.

## Main results

* `SimpleGraph.adjMatrix_map`: the adjacency matrix is preserved by any map sending `0` to `0`
  and `1` to `1`.
* `SimpleGraph.degMatrix_map`: the degree matrix is preserved by any additive map sending `1`
  to `1`.
* `SimpleGraph.adjMatrix_sq_apply`: the `(v, w)` entry of `A²` is the number of common neighbours
  of `v` and `w`.
* `SimpleGraph.det_submatrix_adjMatrix_fin_two`, `SimpleGraph.det_submatrix_adjMatrix_fin_three`:
  the minors of the adjacency matrix along a family of two or three vertices.
* `SimpleGraph.det_submatrix_adjMatrix_of_card_eq_one`,
  `SimpleGraph.det_submatrix_adjMatrix_of_card_eq_two`,
  `SimpleGraph.det_submatrix_adjMatrix_of_card_eq_three`: the principal minors of the adjacency
  matrix of orders `1`, `2` and `3`.
* `SimpleGraph.adjMatrix_sup_of_disjoint`, `SimpleGraph.degMatrix_sup_of_disjoint`,
  `SimpleGraph.lapMatrix_sup_of_disjoint`: the matrices of the union of two edge-disjoint graphs
  are the sums of their matrices.
* `SimpleGraph.lapMatrix_sdiff_of_le`: for `G ≤ H`, `L(H \ G) = L(H) - L(G)`.
-/

public section

open Matrix

namespace SimpleGraph

variable {V R S F : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] [FunLike F R S]

/-- The adjacency matrix is preserved by any map sending `0` to `0` and `1` to `1`. -/
@[simp]
theorem adjMatrix_map [Zero R] [One R] [Zero S] [One S] [ZeroHomClass F R S] [OneHomClass F R S]
    (f : F) : (G.adjMatrix R).map f = G.adjMatrix S := by
  ext v w
  simp [apply_ite f]

/-- The degree matrix is preserved by any additive map sending `1` to `1`. -/
@[simp]
theorem degMatrix_map [AddMonoidWithOne R] [AddMonoidWithOne S] [AddMonoidHomClass F R S]
    [OneHomClass F R S] [Fintype V] [DecidableEq V] (f : F) :
    (G.degMatrix R).map f = G.degMatrix S := by
  ext v w
  simp [degMatrix, diagonal_apply, apply_ite f, map_natCast' f (map_one f)]

/-- The `(v, w)` entry of the square of the adjacency matrix is the number of common neighbours
of `v` and `w`; on the diagonal this is the degree of `v`. -/
theorem adjMatrix_sq_apply [Fintype V] [DecidableEq V] [Semiring R] (v w : V) :
    (G.adjMatrix R ^ 2) v w = Fintype.card (G.commonNeighbors v w) := by
  rw [sq, adjMatrix_mul_apply, Fintype.card_subtype]
  simp only [adjMatrix_apply, Finset.sum_boole]
  congr 2
  ext u
  simp [commonNeighbors, adj_comm]

/-! ### Small minors -/

section Minors

open Finset

variable (G) [CommRing R]

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

section Principal

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

end Principal

end Minors

/-! ### Edge-disjoint unions -/

section Disjoint

variable (R) {H : SimpleGraph V} [DecidableRel H.Adj]

/-- The adjacency matrix of the union of two edge-disjoint graphs is the sum of their adjacency
matrices. -/
theorem adjMatrix_sup_of_disjoint [AddZeroClass R] [One R] [DecidableRel (G ⊔ H).Adj]
    (h : Disjoint G H) : (G ⊔ H).adjMatrix R = G.adjMatrix R + H.adjMatrix R := by
  ext v w
  by_cases hG : G.Adj v w
  · have hH : ¬H.Adj v w := disjoint_left.mp h v w hG
    simp [hG, hH]
  · by_cases hH : H.Adj v w <;> simp [hG, hH]

/-- The degree matrix of the union of two edge-disjoint graphs is the sum of their degree
matrices. -/
theorem degMatrix_sup_of_disjoint [AddMonoidWithOne R] [Fintype V] [DecidableEq V]
    [DecidableRel (G ⊔ H).Adj] (h : Disjoint G H) :
    (G ⊔ H).degMatrix R = G.degMatrix R + H.degMatrix R := by
  simp only [degMatrix, diagonal_add, degree_sup_of_disjoint _ h, Nat.cast_add]

/-- The Laplacian of the union of two edge-disjoint graphs is the sum of their Laplacians. -/
theorem lapMatrix_sup_of_disjoint [AddGroupWithOne R] [Fintype V] [DecidableEq V]
    [DecidableRel (G ⊔ H).Adj] (h : Disjoint G H) :
    (G ⊔ H).lapMatrix R = G.lapMatrix R + H.lapMatrix R := by
  rw [lapMatrix.eq_1 R (G ⊔ H), degMatrix_sup_of_disjoint R h, adjMatrix_sup_of_disjoint R h]
  -- `R` need not be commutative, but the matrices involved commute: their entries are casts.
  refine AddCommute.add_sub_add_comm (Matrix.ext fun v w => ?_) (Matrix.ext fun v w => ?_) <;>
    by_cases hG : G.Adj v w
  · simp [hG, disjoint_left.mp h v w hG]
  · simp [hG]
  · simp [hG, hG.ne, degMatrix]
  · simp [hG]

/-- If `G ≤ H`, the Laplacian of the graph `H \ G` of the edges of `H` not in `G` is the
difference of the Laplacians of `H` and `G`. -/
theorem lapMatrix_sdiff_of_le [AddGroupWithOne R] [Fintype V] [DecidableEq V]
    [DecidableRel (H \ G).Adj] (h : G ≤ H) :
    (H \ G).lapMatrix R = H.lapMatrix R - G.lapMatrix R := by
  have hsup : H.lapMatrix R = (H \ G ⊔ G).lapMatrix R := by
    -- The two sides differ only in the graph, `H = H \ G ⊔ G`, and its decidability instance.
    congr!
    exact (sdiff_sup_cancel h).symm
  rw [hsup, lapMatrix_sup_of_disjoint R disjoint_sdiff_self_left, add_sub_cancel_right]

end Disjoint

end SimpleGraph
