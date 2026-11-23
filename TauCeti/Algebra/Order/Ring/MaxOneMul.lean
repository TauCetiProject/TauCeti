/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Absorbing a factor into `max 1 c`

If one of two nonnegative summands is multiplied by a factor `c`, the sum grows by at most the
factor `max 1 c`: `a + c * b ≤ max 1 c * (a + b)`. This is how a constant on one term of a norm
or of an a priori bound is absorbed into a constant on the whole sum.

## Main results

* `TauCeti.add_mul_le_max_one_mul_add`: the inequality above.
-/

public section

namespace TauCeti

variable {R : Type*} [Semiring R] [LinearOrder R] [IsOrderedRing R]

/-- If the nonnegative summand `b` is multiplied by `c`, the sum `a + b` grows by at most the
factor `max 1 c`: `a + c * b ≤ max 1 c * (a + b)` for `0 ≤ a` and `0 ≤ b`. -/
theorem add_mul_le_max_one_mul_add {a b c : R} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a + c * b ≤ max 1 c * (a + b) := by
  rw [mul_add]
  exact add_le_add (le_mul_of_one_le_left ha (le_max_left _ _))
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hb)

end TauCeti
