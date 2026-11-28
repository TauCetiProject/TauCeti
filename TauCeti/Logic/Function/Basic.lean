/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Function.Defs
import Mathlib.Basic.Logic.Basic

/-!
# Basic facts about functions

Two distinct dependent functions witness that their domain is nonempty (`Function.nonempty_of_ne`).
A function that is a retract of a bijection is bijective (`Function.bijective_of_retract`). A map
into a subtype whose values are those of an injective map is injective
(`Function.Injective.of_val_eq`). If every pair of inputs agrees under one of two maps,
then one map is constant (`Function.forall_eq_or_forall_eq_of_forall_eq_or_eq`).
-/

public section

namespace Function

/-- Two distinct dependent functions witness that their domain is nonempty. -/
theorem nonempty_of_ne {α : Sort*} {β : α → Sort*} {f₁ f₂ : ∀ a, β a} (h : f₁ ≠ f₂) :
    Nonempty α :=
  Classical.byContradiction fun hn ↦ h (funext fun a ↦ (hn ⟨a⟩).elim)

/-- A map `Φ` that is a retract of a bijection `Φ'` is bijective: if `a`, `b` embed the source
and target of `Φ` into those of `Φ'` with retractions `c`, `d`, `Φ'` restricts to `Φ` along them
in both directions. -/
theorem bijective_of_retract {A B A' B' : Type*} {Φ : A → B} {Φ' : A' → B'} {a : A → A'}
    {c : A' → A} {b : B → B'} {d : B' → B} (hΦ' : Bijective Φ')
    (ha : ∀ z, Φ' (a z) = b (Φ z)) (hb : ∀ z, Φ (c z) = d (Φ' z)) (hc : LeftInverse c a)
    (hd : LeftInverse d b) : Bijective Φ :=
  ⟨fun z z' h ↦ by rw [← hc z, ← hc z', hΦ'.1 ((ha z).trans (h ▸ (ha z').symm))],
    fun g ↦ by
      obtain ⟨z, hz⟩ := hΦ'.2 (b g)
      exact ⟨c z, by rw [hb, hz, hd]⟩⟩

/-- A map `g` into a subtype is injective when its values are those of an injective map `f`. -/
theorem Injective.of_val_eq {α β : Sort*} {p : β → Prop} {f : α → β} {g : α → Subtype p}
    (hf : Injective f) (h : ∀ a, (g a : β) = f a) : Injective g :=
  fun a b hab => hf (by rw [← h, ← h, hab])

/-- If every pair of inputs agrees under one of two maps, one of the maps is constant. -/
theorem forall_eq_or_forall_eq_of_forall_eq_or_eq {ι α β : Sort*} {a : ι → α} {b : ι → β}
    (h : ∀ i j, a i = a j ∨ b i = b j) :
    (∀ i j, a i = a j) ∨ (∀ i j, b i = b j) := by
  classical
  by_cases ha : ∀ i j, a i = a j
  · exact Or.inl ha
  obtain ⟨i, hi⟩ := not_forall.mp ha
  obtain ⟨j, hij⟩ := not_forall.mp hi
  have hbij := (h i j).resolve_left hij
  have hb (k : ι) : b k = b i := by
    rcases h i k with hik | hik
    · have hjk : a j ≠ a k := fun hjk ↦ hij (hik.trans hjk.symm)
      exact ((h j k).resolve_left hjk).symm.trans hbij.symm
    · exact hik.symm
  exact Or.inr fun k l ↦ (hb k).trans (hb l).symm

end Function
