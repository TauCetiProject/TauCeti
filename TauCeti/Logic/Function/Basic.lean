/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Function.Defs

/-!
# Basic facts about functions

* `Function.bijective_of_retract`: a function that is a retract of a bijection is bijective.
* `Function.Injective.of_comp_eq`: if `g ∘ f` agrees pointwise with an injective map `f'`, then
  `f` is injective.
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

/-- If `g ∘ f` agrees pointwise with an injective map `f'`, then `f` is injective. This is
`Function.Injective.of_comp` when the factorization is given as a pointwise identity
`∀ x, g (f x) = f' x` (for instance between bundled homomorphisms). -/
theorem Injective.of_comp_eq {α β γ : Sort*} {f : α → β} {g : β → γ} {f' : α → γ}
    (hf' : Injective f') (h : ∀ x, g (f x) = f' x) : Injective f :=
  fun _ _ hab ↦ hf' (by rw [← h, ← h, hab])

end Function
