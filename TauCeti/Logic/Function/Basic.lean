/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Function.Defs

/-!
# Basic facts about functions

A function that is a retract of a bijection is bijective (`Function.bijective_of_retract`). A map
into a subtype whose values are those of an injective map is injective
(`Function.Injective.of_val_eq`).
-/

public section

namespace Function

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

end Function
