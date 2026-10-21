/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Basic

/-!
# Divisibility and ratio bounds for natural numbers

Convert integer multiples with bounded natural coefficients into natural-number divisibility
and bounds.
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

end TauCeti.Nat
