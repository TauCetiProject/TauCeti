/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Disjointed
import Mathlib.Data.Fin.VecNotation

/-!
# Disjointed finite prepended families

Computes `disjointed (Fin.cons a u)` in any generalized Boolean algebra at `0`
(`disjointed_cons_zero`) and at `i.succ` (`disjointed_cons_succ`).
-/

public section

open Finset

section GeneralizedBooleanAlgebra

variable {α : Type*} [GeneralizedBooleanAlgebra α] {n : ℕ}

/-- Disjointing a prepended finite family leaves the prepended first element unchanged. -/
@[simp]
theorem disjointed_cons_zero (a : α) (u : Fin n → α) :
    disjointed (Fin.cons a u) 0 = a := by
  rw [← bot_eq_zero, disjointed_bot, bot_eq_zero, Fin.cons_zero]

/-- Disjointing a prepended finite family at `i.succ` removes the prepended element `a` from
`disjointed u i`. -/
@[simp]
theorem disjointed_cons_succ (a : α) (u : Fin n → α) (i : Fin n) :
    disjointed (Fin.cons a u) i.succ = disjointed u i \ a := by
  have hIio : Iio i.succ = insert 0 ((Iio i).map (Fin.succEmb n)) := by
    ext j
    refine Fin.cases ?_ (fun k ↦ ?_) j <;> simp
  rw [disjointed_apply, disjointed_apply, Fin.cons_succ, hIio, sup_insert, sup_map,
    Fin.cons_zero, sdiff_sdiff_left, sup_comm]
  simp

end GeneralizedBooleanAlgebra
