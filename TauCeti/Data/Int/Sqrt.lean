/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Sqrt
import Mathlib.Tactic.Linarith

/-!
# The integer square root brackets its argument

Mathlib's `Int.sqrt z` is `Nat.sqrt z.toNat`: the largest `r` with `r * r ≤ z` when `z ≥ 0`, and
`0` when `z < 0`. This file transfers the bracketing inequalities of `Nat.sqrt` to it, so that
`Int.sqrt z` is the floor of the real square root of a nonnegative integer `z`.
-/

public section

namespace Int

/-- The integer square root of a nonpositive integer is `0`. -/
theorem sqrt_eq_zero_of_nonpos {z : ℤ} (hz : z ≤ 0) : sqrt z = 0 := by
  rw [sqrt, Int.toNat_of_nonpos hz, Nat.sqrt_zero, Nat.cast_zero]

/-- The square of `Int.sqrt z` is at most `z`, for `z ≥ 0`. -/
theorem sqrt_mul_sqrt_le {z : ℤ} (hz : 0 ≤ z) : sqrt z * sqrt z ≤ z := by
  have h : ((z.toNat.sqrt * z.toNat.sqrt : ℕ) : ℤ) ≤ z.toNat := by exact_mod_cast Nat.sqrt_le _
  rw [Int.toNat_of_nonneg hz] at h
  rw [sqrt]
  exact_mod_cast h

/-- `z` is less than the square of `Int.sqrt z + 1`. -/
theorem lt_sqrt_add_one_mul_sqrt_add_one (z : ℤ) : z < (sqrt z + 1) * (sqrt z + 1) := by
  have h := Nat.lt_succ_sqrt z.toNat
  rw [sqrt]
  calc z ≤ z.toNat := Int.self_le_toNat z
    _ < _ := by exact_mod_cast h

/-- An integer whose square is at most `z` is at most `Int.sqrt z`. -/
theorem le_sqrt_of_mul_self_le {m z : ℤ} (h : m * m ≤ z) : m ≤ sqrt z := by
  by_contra hlt
  have h₀ := sqrt_nonneg z
  have h₁ := lt_sqrt_add_one_mul_sqrt_add_one z
  have h₂ : sqrt z + 1 ≤ m := not_le.mp hlt
  nlinarith

end Int
