/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CompleteMultipartite

/-!
# Common neighbours in complete equipartite graphs

The complete equipartite graph `K_{m × a}` (Mathlib's `SimpleGraph.completeEquipartiteGraph m a`)
has the vertex set `Fin m × Fin a`, and two vertices are adjacent when they lie in different
parts, that is, when their first coordinates differ. Its complement `m K_a` is the disjoint union
of `m` complete graphs on `a` vertices. This file describes the common neighbours in both graphs
and the degrees of the complement. These counts are what the strong regularity of both graphs
needs.

## Main results

* `SimpleGraph.commonNeighbors_completeEquipartiteGraph`: the common neighbours of `v` and `w`
  in `K_{m × a}` are the vertices outside the parts of `v` and `w`.
* `SimpleGraph.commonNeighbors_compl_completeEquipartiteGraph`: the common neighbours of `v` and
  `w` in `m K_a` are the other vertices of their common part, if they have one.
* `SimpleGraph.degree_compl_completeEquipartiteGraph`: every vertex of `m K_a` has degree
  `a - 1`.
-/

public section

namespace SimpleGraph

variable {m a : ℕ}

/-- The common neighbours of `v` and `w` in `K_{m × a}` are the vertices whose part is neither
the part of `v` nor the part of `w`. -/
theorem commonNeighbors_completeEquipartiteGraph (v w : Fin m × Fin a) :
    (completeEquipartiteGraph m a).commonNeighbors v w = {v.1, w.1}ᶜ ×ˢ Set.univ := by
  ext u
  simp [commonNeighbors, ne_comm]

/-- The common neighbours of `v` and `w` in the complement `m K_a` of `K_{m × a}` are the
vertices other than `v` and `w` that lie in the part of `v` and in the part of `w`. This set is
empty when the two parts differ. -/
theorem commonNeighbors_compl_completeEquipartiteGraph (v w : Fin m × Fin a) :
    (completeEquipartiteGraph m a)ᶜ.commonNeighbors v w =
      (({v.1} ∩ {w.1}) ×ˢ Set.univ) \ {v, w} := by
  ext u
  simp only [commonNeighbors, Set.mem_inter_iff, mem_neighborSet, compl_adj,
    completeEquipartiteGraph_adj, not_not, Set.mem_sdiff, Set.mem_prod, Set.mem_singleton_iff,
    Set.mem_univ, and_true, Set.mem_insert_iff]
  grind

/-- Every vertex of the complement `m K_a` of `K_{m × a}` has degree `a - 1`. -/
theorem degree_compl_completeEquipartiteGraph (v : Fin m × Fin a) :
    (completeEquipartiteGraph m a)ᶜ.degree v = a - 1 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Fin.pos v.1).ne'
  rw [degree_compl, degree_completeEquipartiteGraph, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, Nat.add_sub_cancel, add_one_mul]
  omega

end SimpleGraph
