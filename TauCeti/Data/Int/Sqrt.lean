/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Data.Int.Order.Lemmas
public import Mathlib.Data.Int.Sqrt

/-!
# The integer square root brackets its argument

Mathlib's `Int.sqrt z` is `Nat.sqrt z.toNat`: the largest `r` with `r * r ≤ z` when `z ≥ 0`, and
`0` when `z < 0`. Mathlib's `Int.abs_le_sqrt` gives the lower bracket `sqrt z * sqrt z ≤ z`; this
file adds the upper bracket `z < (sqrt z + 1) * (sqrt z + 1)`, transferred from `Nat.sqrt`, and the
strict lower bracket for nonsquare `z`. So `Int.sqrt z` is the floor of the real square root of a
nonnegative integer `z`.
-/

public section

namespace Int

/-- The integer square root of a nonpositive integer is `0`. -/
theorem sqrt_eq_zero_of_nonpos {z : ℤ} (hz : z ≤ 0) : sqrt z = 0 := by
  rw [sqrt, Int.toNat_of_nonpos hz, Nat.sqrt_zero, Nat.cast_zero]

/-- `z` is less than the square of `Int.sqrt z + 1`. -/
theorem lt_sqrt_add_one_mul_sqrt_add_one (z : ℤ) : z < (sqrt z + 1) * (sqrt z + 1) := by
  have h := Nat.lt_succ_sqrt z.toNat
  rw [sqrt]
  calc z ≤ z.toNat := Int.self_le_toNat z
    _ < _ := by exact_mod_cast h

/-- The square of `Int.sqrt z` is less than a nonsquare `z ≥ 0`. -/
theorem sqrt_mul_sqrt_lt {z : ℤ} (hz : ¬ IsSquare z) (h₀ : 0 ≤ z) : sqrt z * sqrt z < z :=
  ((abs_le_sqrt h₀).1 (abs_of_nonneg (sqrt_nonneg z)).le).lt_of_ne fun h ↦ hz ⟨_, h.symm⟩

end Int
