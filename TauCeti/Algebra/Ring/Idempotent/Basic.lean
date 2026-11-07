/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.Abel

/-!
# The involution attached to an idempotent

For an idempotent `p` of a ring, `2 p - 1` squares to `1`. For a star projection this is the
self-adjoint unitary `IsStarProjection.two_mul_sub_one_mem_unitary`.

## Main results

* `IsIdempotentElem.two_mul_sub_one_mul_self`: `(2 p - 1) * (2 p - 1) = 1`.
-/

public section

namespace IsIdempotentElem

variable {R : Type*} [Ring R] {p : R}

/-- For an idempotent `p`, `2 p - 1` squares to `1`. -/
theorem two_mul_sub_one_mul_self (hp : IsIdempotentElem p) : (2 * p - 1) * (2 * p - 1) = 1 := by
  simp only [two_mul, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, hp.eq]
  abel

end IsIdempotentElem
