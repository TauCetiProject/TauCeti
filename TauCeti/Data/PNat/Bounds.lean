/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.PNat.Basic

/-!
# Divisibility and ratio bounds for positive natural numbers

Convert the small integer multiple patterns used in numerical-type classification into
natural-number divisibility and bounds.
-/

public section

namespace TauCeti.PNat

/-- If `(a : ℤ)` is one of `1, 2, 3, 4` times `(b : ℤ)`, then `(b : ℕ)` divides `a` with quotient
at most `4`. -/
lemma dvd_and_le_four_of_int {a b : ℕ+}
    (h : (a : ℤ) = b ∨ (a : ℤ) = 2 * b ∨ (a : ℤ) = 3 * b ∨ (a : ℤ) = 4 * b) :
    (b : ℕ) ∣ a ∧ (a : ℕ) ≤ 4 * b := by
  rcases h with h | h | h | h <;>
    [exact ⟨⟨1, by omega⟩, by omega⟩; exact ⟨⟨2, by omega⟩, by omega⟩;
      exact ⟨⟨3, by omega⟩, by omega⟩; exact ⟨⟨4, by omega⟩, by omega⟩]

/-- If `(a : ℤ)` is one of `1, …, 6` times `(b : ℤ)`, then `(b : ℕ)` divides `a` with quotient
at most `6`. -/
lemma dvd_and_le_six_of_int {a b : ℕ+}
    (h : (a : ℤ) = b ∨ (a : ℤ) = 2 * b ∨ (a : ℤ) = 3 * b ∨
      (a : ℤ) = 4 * b ∨ (a : ℤ) = 5 * b ∨ (a : ℤ) = 6 * b) :
    (b : ℕ) ∣ a ∧ (a : ℕ) ≤ 6 * b := by
  rcases h with h | h | h | h | h | h <;>
    [exact ⟨⟨1, by omega⟩, by omega⟩; exact ⟨⟨2, by omega⟩, by omega⟩;
      exact ⟨⟨3, by omega⟩, by omega⟩; exact ⟨⟨4, by omega⟩, by omega⟩;
      exact ⟨⟨5, by omega⟩, by omega⟩; exact ⟨⟨6, by omega⟩, by omega⟩]

end TauCeti.PNat
