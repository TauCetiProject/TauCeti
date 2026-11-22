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

Computes `disjointed (Fin.cons a u) i.succ` in any generalized Boolean algebra
(`disjointed_cons_succ`).
-/

public section

open Finset

section GeneralizedBooleanAlgebra

variable {α : Type*} [GeneralizedBooleanAlgebra α] {n : ℕ}

/-- Disjointing a prepended finite family at `i.succ` removes the prepended element `a` from
`disjointed u i`. -/
@[simp]
theorem disjointed_cons_succ (a : α) (u : Fin n → α) (i : Fin n) :
    disjointed (Fin.cons a u) i.succ = disjointed u i \ a := by
  rw [disjointed_apply, disjointed_apply, Fin.cons_succ, ← Ico_bot, bot_eq_zero,
    ← insert_left_Ioo (Fin.succ_pos i), ← Fin.map_succEmb_Iio, sup_insert, sup_map,
    Fin.cons_zero, sdiff_sdiff_left, sup_comm]
  simp

end GeneralizedBooleanAlgebra
