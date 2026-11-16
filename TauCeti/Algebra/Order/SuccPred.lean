/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Order.SuccPred.Basic

/-!
# Successors in ordered additive groups

In an ordered additive group the translations `x ↦ a + x` are order isomorphisms, so they commute
with the successor function: `a + succ b = succ (a + b)`. In particular `succ a = a + succ 0`, so
the successor function of a discretely ordered abelian group is translation by its least positive
element `succ 0`. Unlike Mathlib's `SuccAddOrder`, this does not ask the instance `One` to be that
element: on `Lex (Fin n → ℤ)` the instance `One` is the constant function `1`, which is not the
least positive element when `n ≥ 2`.
-/

public section

namespace TauCeti.Order

open _root_.Order

variable {α : Type*} [AddGroup α] [PartialOrder α] [AddLeftMono α] [SuccOrder α]

/-- Translations commute with the successor function. -/
theorem add_succ (a b : α) : a + succ b = succ (a + b) :=
  (OrderIso.addLeft a).map_succ b

/-- The successor of `a` is `a` plus the least positive element `succ 0`. -/
theorem succ_eq_add_succ_zero (a : α) : succ a = a + succ 0 := by
  rw [add_succ, add_zero]

end TauCeti.Order
