/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import TauCeti.Combinatorics.SimpleGraph.Finite

/-!
# The adjacency, degree and Laplacian matrices

The adjacency matrix `G.adjMatrix R` and the degree matrix `G.degMatrix R` of a simple graph have
entries built from `0`, `1` and natural-number casts, so applying a coefficient map entrywise
gives the same matrix over the target ring. The entries of the square of the adjacency matrix
count common neighbours.

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
