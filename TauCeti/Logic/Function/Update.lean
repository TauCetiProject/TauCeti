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
* `Set.injOn_update_of_injOn_diff`: a map injective off a point `a` of a set, whose value `L` at `a`
  is taken nowhere else on the set, stays injective after being redefined to be `L` at `a`.
* `Function.update_id_apply_eq_iff`: `Function.update id b a` takes the value `a` exactly at `a`
  and `b`.
* `Function.update_id_apply_eq_update_id_apply_iff`, `Function.update_id_swap_apply`: two points
  have the same image under `Function.update id b a` exactly when they agree up to
  `Equiv.swap a b`.
* `Function.Embedding.update_id_comp_eq_update_id_comp_iff`: two embeddings have the same
  composite with `Function.update id b a` exactly when they agree up to `Equiv.swap a b`.
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

namespace Function.Embedding

variable {a b : α}

/-- Two embeddings `f` and `g` have the same composite with `update id b a` exactly when `g` is `f`
or `Equiv.swap a b ∘ f`. -/
theorem update_id_comp_eq_update_id_comp_iff {ι : Type*} (f g : ι ↪ α) :
    update id b a ∘ g = update id b a ∘ f ↔ g = f ∨ g = f.trans (Equiv.swap a b).toEmbedding := by
  constructor
  · intro h
    have hpt (i : ι) : g i = f i ∨ g i = Equiv.swap a b (f i) :=
      update_id_apply_eq_update_id_apply_iff.1 (congrFun h i)
    by_contra hne
    simp only [not_or, DFunLike.ext_iff, not_forall, Embedding.trans_apply,
      Equiv.coe_toEmbedding] at hne
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hne
    have hi' : g i = Equiv.swap a b (f i) := (hpt i).resolve_left hi
    have hj' : g j = f j := (hpt j).resolve_right hj
    -- Both `f i` and `f j` are moved by the swap, so they are `a` and `b` in some order, and
    -- then `g i = g j`.
    have hfi : f i = a ∨ f i = b :=
      (Equiv.swap_apply_ne_self_iff.1 fun h => hi (hi'.trans h)).2
    have hfj : f j = a ∨ f j = b :=
      (Equiv.swap_apply_ne_self_iff.1 fun h => hj (hj'.trans h.symm)).2
    have hij : i ≠ j := by
      rintro rfl
      exact hi hj'
    have hfij : f i ≠ f j := f.injective.ne hij
    apply g.injective.ne hij
    rw [hi', hj']
    rcases hfi with hfi | hfi <;> rcases hfj with hfj | hfj <;>
      simp_all [Equiv.swap_apply_left, Equiv.swap_apply_right]
  · rintro (rfl | rfl)
    · rfl
    · funext i
      exact update_id_swap_apply (f i)

end Function.Embedding
