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
`a² + a b + b²` are coprime. Modulo `a`, `b` and `a + b` the second product is `b²`, `a²` and
`-a b`, each of them coprime to the respective modulus.

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

/-- **For coprime `a` and `b`, the products `a b (a + b)` and `a² + a b + b²` are coprime**:
modulo `a`, `b` and `a + b` the second is `b²`, `a²` and `-a b`. -/
theorem IsCoprime.mul_mul_add_sq_add_mul_add_sq (h : IsCoprime a b) :
    IsCoprime (a * b * (a + b)) (a ^ 2 + a * b + b ^ 2) := by
  refine IsCoprime.symm (IsCoprime.mul_right (IsCoprime.mul_right ?_ ?_) ?_)
  · -- `a² + a b + b² ≡ b² (mod a)`
    rw [show a ^ 2 + a * b + b ^ 2 = b ^ 2 + a * (a + b) by ring, IsCoprime.add_mul_left_left_iff]
    exact h.symm.pow_left
  · -- `a² + a b + b² ≡ a² (mod b)`
    rw [show a ^ 2 + a * b + b ^ 2 = a ^ 2 + b * (a + b) by ring, IsCoprime.add_mul_left_left_iff]
    exact h.pow_left
  · -- `a² + a b + b² ≡ -a b (mod a + b)`
    rw [show a ^ 2 + a * b + b ^ 2 = -(a * b) + (a + b) * (a + b) by ring,
      IsCoprime.add_mul_left_left_iff, IsCoprime.neg_left_iff]
    refine IsCoprime.mul_left ?_ ?_
    · simpa [add_comm] using h.add_mul_left_right 1
    · simpa [add_comm] using h.symm.add_mul_left_right 1
