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
finitely many coordinates of a tuple.

## Main results

* `Finset.forall_notMem_iff_forall_notMem_insert`: a property holds away from `s` iff it holds
  away from `insert a s` and at `a`, for `a ∉ s`.
* `Function.forall_notMem_update_eq_iff_of_mem`: updating `f` at a point of `S` does not change
  where it agrees with `g` away from `S`.
* `Function.forall_notMem_update_eq_iff_of_notMem`: updating `f` at a point `a ∉ S` to `b` agrees
  with `g` away from `S` iff `f` agrees with `g` away from `insert a S` and `b = g a`.
-/

public section

variable {α : Type*} [DecidableEq α]

namespace Finset

/-- A property holds away from `s` iff it holds away from `insert a s` and at `a`, for `a ∉ s`. -/
theorem forall_notMem_iff_forall_notMem_insert {s : Finset α} {a : α} {p : α → Prop}
    (h : a ∉ s) : (∀ x ∉ s, p x) ↔ (∀ x ∉ insert a s, p x) ∧ p a := by
  refine ⟨fun H ↦ ⟨fun x hx ↦ H x fun hs ↦ hx (mem_insert_of_mem hs), H a h⟩, ?_⟩
  rintro ⟨H, ha⟩ x hx
  by_cases hxa : x = a
  · exact hxa ▸ ha
  · exact H x (by simp [hxa, hx])

end Finset

namespace Function

variable {β : α → Type*} {S : Finset α} {a : α} {f g : ∀ x, β x} {b : β a}

/-- Updating `f` at a point of `S` does not change where it agrees with `g` away from `S`. -/
@[simp] theorem forall_notMem_update_eq_iff_of_mem (h : a ∈ S) :
    (∀ x ∉ S, update f a b x = g x) ↔ ∀ x ∉ S, f x = g x := by
  refine forall₂_congr fun x hx ↦ ?_
  rw [update_of_ne (by rintro rfl; exact hx h)]

/-- Updating `f` at a point `a ∉ S` to `b` agrees with `g` away from `S` iff `f` agrees with `g`
away from `insert a S` and `b = g a`. -/
@[simp] theorem forall_notMem_update_eq_iff_of_notMem (h : a ∉ S) :
    (∀ x ∉ S, update f a b x = g x) ↔ (∀ x ∉ insert a S, f x = g x) ∧ b = g a := by
  rw [Finset.forall_notMem_iff_forall_notMem_insert h,
    forall_notMem_update_eq_iff_of_mem (Finset.mem_insert_self a S), update_self]

end Function
