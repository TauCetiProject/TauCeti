/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Algebra.Ring.Prod

/-!
# Binary product ring and coordinate identities

Over a ring with invertible `2`, the half-sum and half-difference of a pair have sum and difference
equal to that pair (`Prod.invOf_two_mul_add_sub`). We also record how multiplication in `R × S`
interacts with `AddMonoidHom.inl` and `AddMonoidHom.inr`.
-/

public section

namespace AddMonoidHom

variable {R S : Type*} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]

/-- Left multiplication in `R × S` pulls through `AddMonoidHom.inl` via the first coordinate. -/
theorem mul_inl (x : R × S) (r : R) : x * inl R S r = inl R S (x.1 * r) := by ext <;> simp

/-- Right multiplication in `R × S` pulls through `AddMonoidHom.inl` via the first coordinate. -/
theorem inl_mul (r : R) (x : R × S) : inl R S r * x = inl R S (r * x.1) := by ext <;> simp

/-- Left multiplication in `R × S` pulls through `AddMonoidHom.inr` via the second coordinate. -/
theorem mul_inr (x : R × S) (s : S) : x * inr R S s = inr R S (x.2 * s) := by ext <;> simp

/-- Right multiplication in `R × S` pulls through `AddMonoidHom.inr` via the second coordinate. -/
theorem inr_mul (s : S) (x : R × S) : inr R S s * x = inr R S (s * x.2) := by ext <;> simp

end AddMonoidHom

namespace Prod

variable {R : Type*} [Ring R] [Invertible (2 : R)]

/-- The pair `(⅟2 (x + y), ⅟2 (x - y))` is sent back to `(x, y)` by `(a, b) ↦ (a + b, a - b)`. -/
theorem invOf_two_mul_add_sub (z : R × R) :
    (⅟(2 : R) * (z.1 + z.2) + ⅟(2 : R) * (z.1 - z.2),
      ⅟(2 : R) * (z.1 + z.2) - ⅟(2 : R) * (z.1 - z.2)) = z := by
  ext <;> simp [← mul_add, ← mul_sub, ← two_mul]

end Prod
