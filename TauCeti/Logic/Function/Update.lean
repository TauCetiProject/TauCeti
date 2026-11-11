/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Set.Function

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
  whether it agrees with `g` away from `S`.
* `Function.forall_notMem_update_eq_iff_of_notMem`: updating `f` at a point `a ∉ S` to `b` agrees
  with `g` away from `S` iff `f` agrees with `g` away from `insert a S` and `b = g a`.
* `Set.eqOn_update_of_notMem`: updating a function outside a set preserves its values on the set.
* `Set.injOn_update_of_injOn_diff`: a map injective off a point `a` of a set, whose value `L` at `a`
  is taken nowhere else on the set, stays injective after being redefined to be `L` at `a`.
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

/-- A map that is injective off a point `a` of a set `s`, and whose value `L` at `a` is taken
nowhere else on `s`, stays injective on `s` after being redefined to be `L` at `a`. -/
theorem Set.injOn_update_of_injOn_diff {α β : Type*} [DecidableEq α] {G : α → β} {s : Set α}
    {a : α} {L : β} (hG : Set.InjOn G (s \ {a})) (hL : ∀ x ∈ s, x ≠ a → G x ≠ L) :
    Set.InjOn (Function.update G a L) s := by
  intro x hx y hy h
  by_cases h₁ : x = a <;> by_cases h₂ : y = a
  · rw [h₁, h₂]
  · rw [h₁, Function.update_self, Function.update_of_ne h₂] at h
    exact (hL y hy h₂ h.symm).elim
  · rw [h₂, Function.update_self, Function.update_of_ne h₁] at h
    exact (hL x hx h₁ h).elim
  · rw [Function.update_of_ne h₁, Function.update_of_ne h₂] at h
    exact hG ⟨hx, h₁⟩ ⟨hy, h₂⟩ h
