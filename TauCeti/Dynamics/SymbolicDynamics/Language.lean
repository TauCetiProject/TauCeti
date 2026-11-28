/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Set.Card

/-!
# Words read off a set of one-sided sequences

For a set `F ⊆ ℕ → α` of one-sided sequences, `TauCeti.wordsOf F n` is the set of words
`(x 0, …, x (n - 1))` read off points `x ∈ F`, and `TauCeti.languageCount F n` is their number.
Truncating a word of length `n` to its first `m ≤ n` letters maps the words of length `n` onto
those of length `m`, so for a finite alphabet the counts are monotone in `n`.

## Main definitions

* `TauCeti.wordsOf F n`: the words `(x 0, …, x (n - 1))` of points `x ∈ F`.
* `TauCeti.languageCount F n`: their number.

## Main results

* `TauCeti.languageCount_mono`: the word counts are monotone in `n`.
-/

public section

namespace TauCeti

open Set

variable {α : Type*}

/-- The words of length `n` read off points of `F` at the coordinates `0, …, n - 1`. -/
def wordsOf (F : Set (ℕ → α)) (n : ℕ) : Set (Fin n → α) :=
  (fun x i ↦ x i) '' F

@[simp]
theorem mem_wordsOf {F : Set (ℕ → α)} {n : ℕ} {w : Fin n → α} :
    w ∈ wordsOf F n ↔ ∃ x ∈ F, ∀ i : Fin n, x i = w i := by
  simp [wordsOf, funext_iff]

/-- The number of words of length `n` read off points of `F`. -/
noncomputable def languageCount (F : Set (ℕ → α)) (n : ℕ) : ℕ :=
  (wordsOf F n).ncard

theorem languageCount_def (F : Set (ℕ → α)) (n : ℕ) :
    languageCount F n = (wordsOf F n).ncard :=
  (rfl)

variable [Finite α] (F : Set (ℕ → α))

/-- The number of words read off `F` is monotone in their length. -/
theorem languageCount_mono : Monotone (languageCount F) := by
  intro m n hmn
  have h : wordsOf F m = (fun w : Fin n → α ↦ fun i : Fin m ↦ w (Fin.castLE hmn i)) ''
      wordsOf F n := by
    simp only [wordsOf, image_image, Fin.val_castLE]
  rw [languageCount_def, languageCount_def, h]
  exact ncard_image_le (toFinite _)

end TauCeti
