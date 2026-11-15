/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Parallelogram upper bound in star-ordered rings

In any `StarOrderedRing`, expanding `star (x + y) * (x + y) + star (x - y) * (x - y)` and dropping
the nonnegative term `star (x - y) * (x - y)` yields the operator parallelogram bound
`star (x + y) * (x + y) ≤ 2 • (star x * x + star y * y)`.

## Main results

* `TauCeti.star_add_mul_self_le`: `star (x + y) * (x + y) ≤ 2 • (star x * x + star y * y)`.
-/

public section

namespace TauCeti

/-- In a star-ordered ring, `star (x + y) * (x + y) ≤ 2 • (star x * x + star y * y)` by the
parallelogram identity and nonnegativity of `star (x - y) * (x - y)`. -/
theorem star_add_mul_self_le {R : Type*} [NonUnitalRing R] [StarRing R] [PartialOrder R]
    [StarOrderedRing R] (x y : R) :
    star (x + y) * (x + y) ≤ 2 • (star x * x + star y * y) := by
  have hpar : star (x + y) * (x + y) + star (x - y) * (x - y) =
      2 • (star x * x + star y * y) := by
    rw [two_nsmul]
    simp only [star_add, star_sub]
    noncomm_ring
  rw [← hpar]
  exact le_add_of_nonneg_right (star_mul_self_nonneg (x - y))

end TauCeti
