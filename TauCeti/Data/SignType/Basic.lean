/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Basic.Sign.Basic

/-!
# The sign as a quotient by the absolute value

In a linearly ordered division ring, the sign of `x` is `x / |x|`. This is the division form of
Mathlib's `sign_mul_abs`, and it holds at `0` too, since both sides vanish there.

## Main results

* `TauCeti.sign_eq_div_abs`: `sign x = x / |x|`.
-/

public section

namespace TauCeti

/-- In a linearly ordered division ring, the sign of `x` is `x / |x|`. -/
theorem sign_eq_div_abs {α : Type*} [DivisionRing α] [LinearOrder α] [IsStrictOrderedRing α]
    (x : α) : (SignType.sign x : α) = x / |x| := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [eq_div_iff (abs_ne_zero.2 hx), sign_mul_abs]

end TauCeti
