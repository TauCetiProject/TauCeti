/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Graph distance

This file adds lemmas about the graph distance `SimpleGraph.dist` of
`Mathlib/Combinatorics/SimpleGraph/Metric.lean`.

## Main results

* `SimpleGraph.exists_adj_dist_eq_of_dist_eq_add_one`: a vertex at distance `i + 1` from `x` has
  a neighbour at distance `i` from `x`.
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A vertex at distance `i + 1` from `x` has a neighbour at distance `i` from `x`. -/
theorem exists_adj_dist_eq_of_dist_eq_add_one {x w : V} {i : ℕ} (h : G.dist x w = i + 1) :
    ∃ u, G.Adj u w ∧ G.dist x u = i := by
  obtain ⟨p, hp⟩ := exists_walk_of_dist_ne_zero (by omega : G.dist x w ≠ 0)
  have hnil : ¬p.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
  refine ⟨p.penultimate, Walk.adj_penultimate hnil, le_antisymm ?_ ?_⟩
  · exact (dist_le p.dropLast).trans (by rw [Walk.length_dropLast]; omega)
  · have := (Walk.adj_penultimate hnil).reachable.dist_triangle_right x
    rw [dist_eq_one_iff_adj.mpr (Walk.adj_penultimate hnil)] at this
    omega

end SimpleGraph
