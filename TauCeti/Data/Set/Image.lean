/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Image

/-!
# Images of sets under compositions

This file contains elementary lemmas about images of sets under composed functions.
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

end TauCeti
