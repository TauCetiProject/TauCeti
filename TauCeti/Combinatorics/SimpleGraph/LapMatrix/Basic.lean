/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Additivity of the graph Laplacian

The Laplacian of an edge-disjoint union is the sum of the two Laplacians. In particular,
the Laplacians of a graph and its complement sum to the Laplacian of the complete graph.
-/

public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The Laplacian is additive over the union of two edge-disjoint graphs. -/
theorem lapMatrix_sup_of_disjoint (R : Type*) [AddGroupWithOne R]
    {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj] (h : Disjoint G H) :
    (G ⊔ H).lapMatrix R = G.lapMatrix R + H.lapMatrix R := by
  have hdeg (v : V) : (G ⊔ H).degree v = G.degree v + H.degree v := by
    simp only [degree, neighborFinset_sup_of_disjoint v h, Finset.card_disjUnion]
  ext v w
  rcases eq_or_ne v w with rfl | hvw
  · simp [lapMatrix, degMatrix, hdeg, adjMatrix_apply]
  by_cases hG : G.Adj v w <;> by_cases hH : H.Adj v w
  · exact (Set.disjoint_left.mp (disjoint_neighborSet.mpr h v) hG hH).elim
  all_goals simp [lapMatrix, degMatrix, Matrix.diagonal_apply_ne _ hvw, adjMatrix_apply, hG, hH]

/-- The Laplacians of a graph and its complement sum to the vertex count times the identity
minus the all-ones matrix. -/
theorem lapMatrix_add_lapMatrix_compl (R : Type*) [AddGroupWithOne R] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    G.lapMatrix R + Gᶜ.lapMatrix R = (Fintype.card V : Matrix V V R) - Matrix.of 1 := by
  have htop : (G ⊔ Gᶜ).lapMatrix R = (⊤ : SimpleGraph V).lapMatrix R := by
    congr 1
    exact sup_compl_eq_top
  rw [← lapMatrix_sup_of_disjoint R disjoint_compl_right, htop, lapMatrix_top]

end SimpleGraph
