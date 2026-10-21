/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Basic

/-!
# Divisibility and ratio bounds for natural numbers

Convert the small integer multiple patterns used in numerical-type classification into
natural-number divisibility and bounds.
-/

public section

namespace TauCeti.Nat

/-- An integer multiple with a bounded natural coefficient gives divisibility and the
corresponding bound in the natural numbers. -/
lemma dvd_and_le_mul_of_int {a b k n : ℕ} (hk : k ≤ n)
    (h : (a : ℤ) = (k : ℤ) * b) : b ∣ a ∧ a ≤ n * b := by
  have hab : a = k * b := by exact_mod_cast h
  rw [hab]
  exact ⟨Nat.dvd_mul_left b k, Nat.mul_le_mul_right b hk⟩

/-- If `(a : ℤ)` is one of `1, 2, 3, 4` times `(b : ℤ)`, then `b` divides `a` and `a ≤ 4 * b`. -/
lemma dvd_and_le_four_of_int {a b : ℕ}
    (h : (a : ℤ) = b ∨ (a : ℤ) = 2 * b ∨ (a : ℤ) = 3 * b ∨ (a : ℤ) = 4 * b) :
    b ∣ a ∧ a ≤ 4 * b := by
  rcases h with h | h | h | h
  · exact dvd_and_le_mul_of_int (k := 1) (by decide) (by simpa using h)
  · exact dvd_and_le_mul_of_int (k := 2) (by decide) h
  · exact dvd_and_le_mul_of_int (k := 3) (by decide) h
  · exact dvd_and_le_mul_of_int (k := 4) (by decide) h

/-- If `(a : ℤ)` is one of `1, …, 6` times `(b : ℤ)`, then `b` divides `a` and `a ≤ 6 * b`. -/
lemma dvd_and_le_six_of_int {a b : ℕ}
    (h : (a : ℤ) = b ∨ (a : ℤ) = 2 * b ∨ (a : ℤ) = 3 * b ∨
      (a : ℤ) = 4 * b ∨ (a : ℤ) = 5 * b ∨ (a : ℤ) = 6 * b) :
    b ∣ a ∧ a ≤ 6 * b := by
  rcases h with h | h | h | h | h | h
  · exact dvd_and_le_mul_of_int (k := 1) (by decide) (by simpa using h)
  · exact dvd_and_le_mul_of_int (k := 2) (by decide) h
  · exact dvd_and_le_mul_of_int (k := 3) (by decide) h
  · exact dvd_and_le_mul_of_int (k := 4) (by decide) h
  · exact dvd_and_le_mul_of_int (k := 5) (by decide) h
  · exact dvd_and_le_mul_of_int (k := 6) (by decide) h

end TauCeti.Nat
