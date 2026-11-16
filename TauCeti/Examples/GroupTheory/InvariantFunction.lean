/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

import TauCeti.GroupTheory.InvariantFunction
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.NormNum

/-!
# Noncommutative checks for invariant functions

The function `g ↦ g 2` on permutations of three letters has level the stabilizer of `2`.
Translation by the cycle `(0 1 2)` conjugates that level in the forward direction;
inverse conjugation fails. Two transpositions also distinguish the two orders of
composition of right translations. These finite computations detect convention errors
that cannot be seen on an abelian group or on constant functions.
-/

open Equiv
open TauCeti

/-- Evaluation at a point is invariant under its right stabilizer. -/
example : IsLevelInvariant (MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3))
    (fun g : Perm (Fin 3) ↦ g 2) := by
  rw [isLevelInvariant_iff]
  intro u hu g
  simpa using congrArg g (MulAction.mem_stabilizer_iff.mp hu)

/-- The forward conjugate is a level for the translated evaluation function. -/
example :
    let J := MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3)
    let y : Perm (Fin 3) := swap 0 1 * swap 1 2
    IsLevelInvariant (J.map (MulAut.conj y))
      (rightTranslate y (fun g : Perm (Fin 3) ↦ g 2)) := by
  dsimp only
  apply IsLevelInvariant.rightTranslate
  rw [isLevelInvariant_iff]
  intro u hu g
  simpa using congrArg g (MulAction.mem_stabilizer_iff.mp hu)

/-- The inverse conjugate is not a level for this same translated function. -/
example :
    let J := MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3)
    let y : Perm (Fin 3) := swap 0 1 * swap 1 2
    ¬ IsLevelInvariant (J.map (MulAut.conj y⁻¹))
      (rightTranslate y (fun g : Perm (Fin 3) ↦ g 2)) := by
  dsimp only
  intro h
  have hj : swap (0 : Fin 3) 1 ∈ MulAction.stabilizer (Perm (Fin 3)) (2 : Fin 3) := by
    decide
  have heq := isLevelInvariant_iff.mp h _ (Subgroup.mem_map_of_mem _ hj) 1
  norm_num [MulAut.conj_apply, Perm.mul_apply, swap_apply_def] at heq

/-- The two orders of right translation have distinct values on a noncommutative group. -/
example :
    let a : Perm (Fin 3) := swap 0 1
    let b : Perm (Fin 3) := swap 1 2
    let f : Perm (Fin 3) → Fin 3 := fun g ↦ g 0
    rightTranslate a (rightTranslate b f) 1 = 1 ∧
      rightTranslate b (rightTranslate a f) 1 = 2 := by
  simp [Perm.mul_apply, swap_apply_def]

/-- Invariance by the trivial subgroup does not force constancy. -/
example :
    let f : Perm (Fin 3) → Fin 3 := fun g ↦ g 2
    IsLeftInvariant ⊥ f ∧ IsLevelInvariant ⊥ f ∧ f ≠ (fun _ ↦ f 1) := by
  refine ⟨isLeftInvariant_bot _, isLevelInvariant_bot _, ?_⟩
  intro h
  have heq := congrFun h (swap (0 : Fin 3) 2)
  norm_num [swap_apply_def] at heq
