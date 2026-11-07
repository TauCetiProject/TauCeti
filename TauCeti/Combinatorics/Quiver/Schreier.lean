/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.Schreier
public import TauCeti.Combinatorics.Quiver.PathWeight

/-!
# Reading the labels of Schreier paths

Mathlib's `Quiver.SchreierGraph.pathFromWord` traverses a word from right to left,
as required for a left action. `Quiver.SchreierGraph.weight_pathFromWord` identifies
the free-group reading in traversal order with the reversed input word.
This complements Runtian Zhou's Schreier path construction in Mathlib.
-/

public section

namespace Quiver.SchreierGraph

variable {V G S : Type*} [Group G] [MulAction G V]

/-- Reading the signed labels of `pathFromWord` gives the input word in reverse order. -/
theorem weight_pathFromWord (ι : S → G) (a : SchreierGraph V ι) (w : List (S × Bool)) :
    (pathFromWord ι a w).weight
      (fun {x y : Symmetrify (SchreierGraph V ι)} (e : x ⟶ y) =>
        e.elim (fun f => FreeGroup.mk [(f.1, true)])
          (fun f => FreeGroup.mk [(f.1, false)])) = FreeGroup.mk w.reverse := by
  -- Mathlib records the cast endpoints as underlying Schreier vertices. Applying the
  -- transport equalities directly avoids reducible matching across Symmetrify.
  induction w with
  | nil =>
    rw [pathFromWord]
    exact (Quiver.Path.weight_cast _ _ _ _).trans
      ((Quiver.Path.weight_nil _ _).trans FreeGroup.one_eq_mk)
  | cons l w ih =>
    rcases l with ⟨i, b⟩
    cases b
    · rw [pathFromWord]
      refine (Quiver.Path.weight_cast _ _ _ _).trans
        ((Quiver.Path.weight_cons _ _ _).trans ?_)
      exact (congrArg₂ (· * ·) ih (Sum.elim_inr _ _ _)).trans
        (by simp only [FreeGroup.mul_mk, List.reverse_cons])
    · rw [pathFromWord]
      refine (Quiver.Path.weight_cast _ _ _ _).trans
        ((Quiver.Path.weight_cons _ _ _).trans ?_)
      exact (congrArg₂ (· * ·) ih (Sum.elim_inl _ _ _)).trans
        (by simp only [FreeGroup.mul_mk, List.reverse_cons])

end Quiver.SchreierGraph
