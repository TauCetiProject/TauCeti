/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Values of the standard circle character of `ZMod N`

Mathlib's `ZMod.toCircle` sends `j : ZMod N` to `exp (2πij/N)`. This file records its value at
the half-way point of an even level: at level `2n` it sends `n` to `exp (πi) = -1`.

## Main results

* `ZMod.coe_toCircle_natCast_self`: `ZMod.toCircle (n : ZMod (2n)) = -1`.
-/

public section

namespace ZMod

open scoped Real

/-- The standard circle character of `ZMod (2n)` sends `n` to `exp (πi) = -1`. -/
theorem coe_toCircle_natCast_self (n : ℕ) [NeZero n] :
    ((toCircle ((n : ℕ) : ZMod (2 * n)) : Circle) : ℂ) = -1 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [toCircle_natCast, Nat.cast_mul, Nat.cast_two]
  have : 2 * π * Complex.I * n / (2 * n) = π * Complex.I := by
    field_simp
  rw [this, Complex.exp_pi_mul_I]

end ZMod
