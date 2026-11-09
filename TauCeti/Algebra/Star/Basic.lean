/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic

/-!
# Annihilators in rings with a proper star

In a star ring whose star is proper (`IsProperStar`: `star x * x = 0` forces `x = 0`), such as a
C⋆-algebra, an element killed by every two-sided multiplication `star d * X * c` vanishes. This is
how entrywise identities are read off from sesquilinear forms with coefficients in the ring, for
instance for matrices over a C⋆-algebra.

## Main results

* `eq_zero_of_forall_star_mul_mul_eq_zero`: if `star d * X * c = 0` for all `c` and `d`, then
  `X = 0`.
-/

public section

variable {R : Type*} [NonUnitalSemiring R] [StarRing R] [IsProperStar R]

/-- In a star ring with proper star, an element annihilated by every two-sided multiplication
vanishes. -/
theorem eq_zero_of_forall_star_mul_mul_eq_zero {X : R} (h : ∀ c d : R, star d * X * c = 0) :
    X = 0 := by
  have h' : star (X * star X) * (X * star X) = 0 := by
    simpa [star_mul, mul_assoc] using h (star X) (X * star X)
  exact mul_star_self_eq_zero.mp (star_mul_self_eq_zero.mp h')
