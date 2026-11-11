/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Coprimality of the products `a b (a + b)` and `a² + a b + b²`

For coprime elements `a` and `b` of a commutative ring, the products `a b (a + b)` and
`a² + a b + b²` are coprime: the product `a b` and the sum `a + b` are coprime, and
`a² + a b + b²` is `(a + b)² - a b`.

Up to the factors `16`, these products are the square root of the discriminant and the `c₄` of
the Frey–Hellegouarch curve `y² = x (x - a) (x + b)`, whose discriminant is `16 (a b (a + b))²` and
whose `c₄` is `16 (a² + a b + b²)`. So the coprimality says that away from `2` the Frey curve of a
coprime pair has good or multiplicative reduction everywhere.

## Main results

* `IsCoprime.mul_mul_add_sq_add_mul_add_sq`: if `a` and `b` are coprime, so are `a b (a + b)` and
  `a² + a b + b²`.
-/

public section

variable {R : Type*} [CommRing R] {a b : R}

/-- For coprime elements `a` and `b` of a commutative ring, the products `a b (a + b)` and
`a² + a b + b²` are coprime. -/
theorem IsCoprime.mul_mul_add_sq_add_mul_add_sq (h : IsCoprime a b) :
    IsCoprime (a * b * (a + b)) (a ^ 2 + a * b + b ^ 2) := by
  have hab : IsCoprime (a * b) (a + b) :=
    .mul_left (by simpa using h.mul_add_left_right 1) (by simpa using h.symm.add_mul_left_right 1)
  -- `a² + a b + b² = (a + b)² - a b`
  rw [show a ^ 2 + a * b + b ^ 2 = (a + b) ^ 2 + a * b * -1 by ring]
  exact .mul_left (hab.pow_right.add_mul_left_right _)
    (by simpa [sq, IsCoprime.neg_right_iff] using hab.symm)
