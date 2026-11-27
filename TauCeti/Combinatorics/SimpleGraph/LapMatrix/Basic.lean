/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import TauCeti.Combinatorics.SimpleGraph.AdjMatrix

/-!
# Laplacian of a graph complement

The Laplacian of an edge-disjoint union is the sum of the two Laplacians. In particular,
the Laplacians of a graph and its complement sum to the Laplacian of the complete graph.
-/

public section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

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
