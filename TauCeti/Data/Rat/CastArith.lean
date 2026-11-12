/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.LinearCombination

/-!
# Rational arithmetic in a field of characteristic zero

A relation `x + θ y = r` with `x`, `y`, `r` rational and `y` nonzero determines `θ` as a rational
number (`TauCeti.eq_ratCast_div_of_add_mul_eq`).
-/

public section

namespace TauCeti

/-- If `x + θ y = r` in a field `𝕜` of characteristic zero, with `x`, `y`, `r` rational and `y`
nonzero, then `θ` is the rational number `(r - x) / y`. -/
theorem eq_ratCast_div_of_add_mul_eq {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {x y r : ℚ} {θ : 𝕜}
    (hy : y ≠ 0) (h : (x : 𝕜) + θ * y = r) : θ = (((r - x) / y : ℚ) : 𝕜) := by
  push_cast
  rw [eq_div_iff (by exact_mod_cast hy)]
  linear_combination h

end TauCeti
