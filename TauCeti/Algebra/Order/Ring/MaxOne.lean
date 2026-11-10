/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs

/-!
# Absorbing a coefficient into `max 1 k`

For nonnegative `a` and `b`, the weighted sum `a + k * b` is at most `max 1 k * (a + b)`. This
absorbs a constant `k` in front of one term of an estimate into a single constant in front of
the whole sum, as when combining a bound for a homogeneous problem with the error from a
right-hand side.

## Main results

* `TauCeti.add_mul_le_max_one_mul_add`: `a + k * b ≤ max 1 k * (a + b)` for `0 ≤ a` and `0 ≤ b`.
-/

public section

namespace TauCeti

variable {R : Type*} [Semiring R] [LinearOrder R] [IsOrderedRing R]

/-- For `0 ≤ a` and `0 ≤ b`, the sum `a + k * b` is at most `max 1 k * (a + b)`. -/
theorem add_mul_le_max_one_mul_add {a b k : R} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a + k * b ≤ max 1 k * (a + b) :=
  (add_le_add (le_mul_of_one_le_left ha (le_max_left 1 k))
    (mul_le_mul_of_nonneg_right (le_max_right 1 k) hb)).trans_eq (mul_add _ _ _).symm

end TauCeti
