/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Insert

/-!
# Agreement of functions away from a finite set

Two functions `f` and `g` agree away from a finset `S` when `∀ x ∉ S, f x = g x`. This file
records how such an agreement condition changes when a point is added to `S`, and when one of the
functions is updated at a point inside or outside `S`. These are the steps that move an updated
coordinate in and out of a comparison of tuples, as in the matrix entries of operators acting on
finitely many coordinates of a tuple. It also describes the fibres of `Function.update id b a`,
the map that sends `b` to `a` and fixes every other point.

## Main results

* `Finset.forall_notMem_iff_forall_notMem_insert`: a property holds away from `s` iff it holds
  away from `insert a s` and at `a`, for `a ∉ s`.
* `Function.forall_notMem_update_eq_iff_of_mem`: updating `f` at a point of `S` does not change
  whether it agrees with `g` away from `S`.
* `Function.forall_notMem_update_eq_iff_of_notMem`: updating `f` at a point `a ∉ S` to `b` agrees
  with `g` away from `S` iff `f` agrees with `g` away from `insert a S` and `b = g a`.
* `Set.eqOn_update_of_notMem`: updating a function outside a set preserves its values on the set.
* `Function.update_id_apply_eq_iff`: `Function.update id b a` takes the value `a` exactly at `a`
  and `b`.
* `Function.update_id_apply_eq_update_id_apply_iff`, `Function.update_id_swap_apply`: two points
  have the same image under `Function.update id b a` exactly when they agree up to
  `Equiv.swap a b`.
-/

public section

variable {α : Type*} [DecidableEq α]

namespace Finset

/-- A property holds away from `s` iff it holds away from `insert a s` and at `a`, for `a ∉ s`. -/
theorem forall_notMem_iff_forall_notMem_insert {s : Finset α} {a : α} {p : α → Prop}
    (h : a ∉ s) : (∀ x ∉ s, p x) ↔ (∀ x ∉ insert a s, p x) ∧ p a := by
  grind

end Finset

namespace Function

variable {β : α → Type*} {S : Finset α} {a : α} {f g : ∀ x, β x} {b : β a}

/-- Updating `f` at a point of `S` does not change whether it agrees with `g` away from `S`. -/
@[simp] theorem forall_notMem_update_eq_iff_of_mem (h : a ∈ S) :
    (∀ x ∉ S, update f a b x = g x) ↔ ∀ x ∉ S, f x = g x := by
  grind

/-- Updating `f` at a point `a ∉ S` to `b` agrees with `g` away from `S` iff `f` agrees with `g`
away from `insert a S` and `b = g a`. -/
@[simp] theorem forall_notMem_update_eq_iff_of_notMem (h : a ∉ S) :
    (∀ x ∉ S, update f a b x = g x) ↔ (∀ x ∉ insert a S, f x = g x) ∧ b = g a := by
  grind

end Function

/-- Updating a function at a point outside `s` preserves its values on `s`. -/
theorem Set.eqOn_update_of_notMem {β : Type*} {f : α → β} {a : α} {s : Set α}
    (ha : a ∉ s) (b : β) : Set.EqOn f (Function.update f a b) s :=
  fun _ hx ↦ (Function.update_of_ne (ne_of_mem_of_not_mem hx ha) _ _).symm

namespace Function

variable {a b : α}

/-- `update id b a` takes the value `a` exactly at the two points `a` and `b`. -/
@[simp]
theorem update_id_apply_eq_iff {x : α} : update id b a x = a ↔ x = a ∨ x = b := by
  rw [update_apply]
  split_ifs with h <;> simp [h]

/-- Two points have the same image under `update id b a` exactly when they agree up to swapping
`a` and `b`. -/
theorem update_id_apply_eq_update_id_apply_iff {x y : α} :
    update id b a y = update id b a x ↔ y = x ∨ y = Equiv.swap a b x := by
  simp only [update_apply, id_eq, Equiv.swap_apply_def]
  split_ifs <;> grind

/-- `update id b a` is invariant under swapping `a` and `b`. -/
@[simp]
theorem update_id_swap_apply (x : α) :
    update id b a (Equiv.swap a b x) = update id b a x :=
  update_id_apply_eq_update_id_apply_iff.2 (Or.inr rfl)

end Function
