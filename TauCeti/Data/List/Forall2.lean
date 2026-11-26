/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.OfFn

/-!
# Lists related entrywise to `List.ofFn`

The list `f 0, …, f (n - 1)` is related entrywise by `R` to a list `l` exactly when `l` is the list
`g 0, …, g (n - 1)` of a function `g` with `R (f i) (g i)` for every `i`
(`List.forall₂_ofFn_left_iff`). This turns an entrywise condition on lists into a family of
conditions indexed by `Fin n`, one for each entry.
-/

public section

namespace List

variable {α β : Type*} {R : α → β → Prop}

/-- `List.ofFn f` is related entrywise by `R` to a list exactly when that list is `List.ofFn g` for
a function `g` with `R (f i) (g i)` for every `i`. -/
theorem forall₂_ofFn_left_iff {n : ℕ} {f : Fin n → α} {l : List β} :
    Forall₂ R (ofFn f) l ↔ ∃ g : Fin n → β, (∀ i, R (f i) (g i)) ∧ l = ofFn g := by
  simp only [forall₂_iff_get, length_ofFn, get_ofFn]
  refine ⟨fun ⟨hn, h⟩ => ⟨fun i => l.get (Fin.cast hn i), fun ⟨i, hi⟩ => ?_, ?_⟩, ?_⟩
  · simpa only [Fin.cast_mk] using h i hi (hn ▸ hi)
  · exact (ofFn_get l).symm.trans (ofFn_congr hn.symm _)
  · rintro ⟨g, h, rfl⟩
    exact ⟨by simp, fun i h₁ _ => by simpa using h ⟨i, h₁⟩⟩

end List
