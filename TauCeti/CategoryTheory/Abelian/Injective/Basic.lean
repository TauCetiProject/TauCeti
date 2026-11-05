/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Injective objects and split monomorphisms

An object `X` of an abelian category is injective exactly when every monomorphism out of `X`
splits. One direction holds in any category: a retraction of a monomorphism `f : X ⟶ Y` extends
`𝟙 X` along `f`. For the other, a morphism `g : A ⟶ X` is extended along a monomorphism
`f : A ⟶ B` by pushing `f` out along `g`. In an abelian category the leg `X ⟶ pushout f g` is
again a monomorphism, and composing the other leg with a retraction of it extends `g`.

This is how injectivity is checked when splittings are what one can produce, as in a finite
semisimple category, where a monomorphism out of a simple object splits.
-/

public section

namespace TauCeti

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An object of an abelian category is injective exactly when every monomorphism out of it
splits. -/
theorem injective_iff_forall_isSplitMono (X : C) :
    Injective X ↔ ∀ ⦃Y : C⦄ (f : X ⟶ Y) [Mono f], IsSplitMono f := by
  refine ⟨fun _ _ f _ ↦ IsSplitMono.mk' ⟨Injective.factorThru (𝟙 X) f, by simp⟩, fun h ↦ ⟨?_⟩⟩
  intro A B g f _
  -- The pushout of the monomorphism `f` along `g` is a monomorphism out of `X`, so it splits.
  have := h (pushout.inr f g)
  exact ⟨pushout.inl f g ≫ retraction (pushout.inr f g), by
    rw [pushout.condition_assoc, IsSplitMono.id, Category.comp_id]⟩

end TauCeti
