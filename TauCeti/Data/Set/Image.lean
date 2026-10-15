/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Function

/-!
# Images of sets under compositions

This file contains elementary lemmas about images of sets under composed functions.
-/

public section

open Function Set

namespace TauCeti

/-- If `c` maps `A` bijectively onto `S` with the point `ζ ∈ S` deleted, then restoring the value
`g ζ` to the image of `A` under `g ∘ c` recovers the image of `S` under `g`. -/
lemma insert_image_comp_of_bijOn_sdiff_singleton {α β γ : Type*} {c : α → β}
    {g : β → γ} {A : Set α} {S : Set β} {ζ : β} (hc : BijOn c A (S \ {ζ})) (hζ : ζ ∈ S) :
    insert (g ζ) ((g ∘ c) '' A) = g '' S := by
  rw [image_comp, hc.image_eq, ← image_insert_eq, insert_sdiff_singleton, insert_eq_of_mem hζ]

end TauCeti
