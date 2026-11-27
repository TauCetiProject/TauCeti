/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Image

/-!
# Images of sets under compositions

This file contains elementary lemmas about images and ranges of functions and sets, and about
preimages under an injective function of the range of a composition or of a single value.
-/

public section

open Function Set

namespace TauCeti

/-- If `c` maps `A` onto `S` with the point `ζ ∈ S` deleted, then restoring the value `g ζ` to the
image of `A` under `g ∘ c` recovers the image of `S` under `g`. -/
lemma insert_image_comp_of_image_eq_sdiff_singleton {α β γ : Type*} {c : α → β}
    {g : β → γ} {A : Set α} {S : Set β} {ζ : β} (hc : c '' A = S \ {ζ}) (hζ : ζ ∈ S) :
    insert (g ζ) ((g ∘ c) '' A) = g '' S := by
  rw [image_comp, hc, ← image_insert_eq, insert_sdiff_self_of_mem hζ]

/-- If `g'` and `g` are intertwined by `ι` along `f` on `s ∩ A`, `f` maps `s ∩ A` into `B`, and for
`z ∈ s` with `f z ∈ B` the point `g' (f z)` lies in `U` exactly when `z ∈ A`, then the image of
`g '' (s ∩ A)` under `ι` is the part in `U` of the image under `g'` of `f '' s ∩ B`. -/
lemma image_image_inter_eq_inter_image {α β γ δ : Type*} {A s : Set α} {B : Set β} {U : Set δ}
    {f : α → β} {g : α → γ} {g' : β → δ} {ι : γ → δ} (hform : ∀ z ∈ s ∩ A, g' (f z) = ι (g z))
    (hAB : MapsTo f (s ∩ A) B) (hU : ∀ z ∈ s, f z ∈ B → (g' (f z) ∈ U ↔ z ∈ A)) :
    ι '' (g '' (s ∩ A)) = U ∩ g' '' (f '' s ∩ B) := by
  grind [MapsTo]

/-- If every value of `f` lies in the union of the ranges of `g₁`, `g₂`, and `g₃`, and each `gᵢ`
takes values in `Set.range f`, then `Set.range f = Set.range g₁ ∪ Set.range g₂ ∪ Set.range g₃`. -/
lemma range_eq_union_three {α γ₁ γ₂ γ₃ : Sort*} {β : Type*} (f : α → β)
    (g₁ : γ₁ → β) (g₂ : γ₂ → β) (g₃ : γ₃ → β)
    (hf : ∀ a, f a ∈ range g₁ ∨ f a ∈ range g₂ ∨ f a ∈ range g₃)
    (h₁ : ∀ x, g₁ x ∈ range f) (h₂ : ∀ y, g₂ y ∈ range f) (h₃ : ∀ z, g₃ z ∈ range f) :
    range f = range g₁ ∪ range g₂ ∪ range g₃ := by
  refine subset_antisymm (range_subset_iff.mpr fun a => ?_)
    (union_subset (union_subset (range_subset_iff.mpr h₁) (range_subset_iff.mpr h₂))
      (range_subset_iff.mpr h₃))
  rcases hf a with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

end TauCeti

namespace Function.Injective

variable {α β γ : Type*} {f : β → γ}

/-- An injective function `f` pulls the range of `f ∘ g` back to the range of `g`. -/
theorem preimage_range_comp (hf : Injective f) (g : α → β) : f ⁻¹' range (f ∘ g) = range g := by
  rw [range_comp, hf.preimage_image]

/-- The fibre of an injective function `f` over `f a` is `{a}`. -/
theorem preimage_singleton (hf : Injective f) (a : β) : f ⁻¹' {f a} = {a} := by
  rw [← image_singleton, hf.preimage_image]

end Function.Injective
