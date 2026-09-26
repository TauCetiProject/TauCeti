/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Tactic.Ring

/-!
# Sum and difference coordinates

Over a commutative ring with invertible `2`, the half-sum and half-difference of a pair
have sum and difference equal to that pair.
-/

public section

namespace Prod

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- The pair `(⅟2 (x + y), ⅟2 (x - y))` is sent back to `(x, y)` by `(a, b) ↦ (a + b, a - b)`. -/
theorem invOf_two_mul_add_sub (z : R × R) :
    (⅟(2 : R) * (z.1 + z.2) + ⅟(2 : R) * (z.1 - z.2),
      ⅟(2 : R) * (z.1 + z.2) - ⅟(2 : R) * (z.1 - z.2)) = z := by
  refine Prod.ext ?_ ?_ <;> dsimp only
  · calc
      ⅟(2 : R) * (z.1 + z.2) + ⅟(2 : R) * (z.1 - z.2) =
          ⅟(2 : R) * (2 * z.1) := by ring
      _ = z.1 := invOf_mul_cancel_left _ _
  · calc
      ⅟(2 : R) * (z.1 + z.2) - ⅟(2 : R) * (z.1 - z.2) =
          ⅟(2 : R) * (2 * z.2) := by ring
      _ = z.2 := invOf_mul_cancel_left _ _

end Prod
