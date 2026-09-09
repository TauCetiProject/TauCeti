/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Neighbours in a cycle graph

Mathlib's `SimpleGraph.cycleGraph m` joins two elements of `Fin m` exactly when they differ by one,
and states that adjacency as a difference. This file reads the same adjacency in the form a
consumer usually wants: a neighbour of a vertex is its successor or its predecessor, so a vertex
has at most the two neighbours `v + 1` and `v - 1`, and on at least three vertices those two are
distinct and really are neighbours.

## Main results

* `TauCeti.eq_add_one_or_eq_add_one_of_cycleGraph_adj`: adjacent vertices differ by one.
* `TauCeti.cycleGraph_eq_or_eq_or_eq_of_adj`: no vertex has three pairwise distinct neighbours,
  that is, every degree is at most two.
* `TauCeti.cycleGraph_adj_add_one`: on at least three vertices a vertex is adjacent to its
  successor.
* `TauCeti.add_one_add_one_ne_self`: on at least three vertices the two neighbours of a vertex are
  distinct.
-/

public section

namespace TauCeti

open SimpleGraph

variable {m : ℕ} [NeZero m]

/-- **Adjacent vertices of a cycle graph differ by one.** -/
theorem eq_add_one_or_eq_add_one_of_cycleGraph_adj {u v : Fin m} (h : (cycleGraph m).Adj u v) :
    v = u + 1 ∨ u = v + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := NeZero.ne m; omega⟩
  obtain _ | n := n
  · exact absurd h cycleGraph_one_adj
  · rcases cycleGraph_adj.mp h with hd | hd
    · exact Or.inr ((sub_eq_iff_eq_add.mp hd).trans (add_comm 1 v))
    · exact Or.inl ((sub_eq_iff_eq_add.mp hd).trans (add_comm 1 u))

/-- **No vertex of a cycle graph has three pairwise distinct neighbours**: every degree is at most
two. -/
theorem cycleGraph_eq_or_eq_or_eq_of_adj {i j j' j'' : Fin m} (h : (cycleGraph m).Adj i j)
    (h' : (cycleGraph m).Adj i j') (h'' : (cycleGraph m).Adj i j'') :
    j = j' ∨ j' = j'' ∨ j'' = j := by
  rcases eq_add_one_or_eq_add_one_of_cycleGraph_adj h with hj | hj <;>
    rcases eq_add_one_or_eq_add_one_of_cycleGraph_adj h' with hj' | hj' <;>
      rcases eq_add_one_or_eq_add_one_of_cycleGraph_adj h'' with hj'' | hj''
  · exact Or.inl (hj.trans hj'.symm)
  · exact Or.inl (hj.trans hj'.symm)
  · exact Or.inr (Or.inr (hj''.trans hj.symm))
  · exact Or.inr (Or.inl (add_right_cancel (hj'.symm.trans hj'')))
  · exact Or.inr (Or.inl (hj'.trans hj''.symm))
  · exact Or.inr (Or.inr (add_right_cancel (hj''.symm.trans hj)))
  · exact Or.inl (add_right_cancel (hj.symm.trans hj'))
  · exact Or.inl (add_right_cancel (hj.symm.trans hj'))

/-- **Consecutive vertices of a cycle graph on at least three vertices are adjacent.** -/
theorem cycleGraph_adj_add_one (hm : 3 ≤ m) (v : Fin m) : (cycleGraph m).Adj v (v + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  exact cycleGraph_adj.mpr (Or.inr (add_sub_cancel_left v 1))

/-- The underlying natural number of a successor in `Fin m`. -/
private theorem val_add_one (v : Fin m) : ((v + 1 : Fin m) : ℕ) = (v.val + 1) % m := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]

private theorem one_add_one_ne_zero (hm : 3 ≤ m) : (1 : Fin m) + 1 ≠ 0 := by
  have h1 : ((1 : Fin m) : ℕ) = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  rw [Ne, Fin.ext_iff, val_add_one, h1, Fin.val_zero, Nat.mod_eq_of_lt (by omega)]
  omega

/-- **Adding one twice in `Fin m` never returns to the same element** when `3 ≤ m`.  For a cycle
graph this says that the two neighbours of a vertex are distinct. -/
theorem add_one_add_one_ne_self (hm : 3 ≤ m) (v : Fin m) : v + 1 + 1 ≠ v := by
  intro h
  refine one_add_one_ne_zero hm (add_left_cancel (a := v) ?_)
  rw [add_zero, ← add_assoc, h]

end TauCeti
