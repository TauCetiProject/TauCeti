/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Coprimality of binary forms in coprime elements

For coprime elements `a` and `b` of a commutative ring, the products `a b (a + b)` and
`a² + a b + b²` are coprime. Modulo `a`, `b` and `a + b` the second product is `b²`, `a²` and
`-a b`, each of them coprime to the respective modulus.

Up to the factors `16`, these products are the square root of the discriminant and the `c₄` of
the Frey–Hellegouarch curve `y² = x (x - a) (x + b)`, whose discriminant is `16 (a b (a + b))²` and
whose `c₄` is `16 (a² + a b + b²)`. So the coprimality says that away from `2` the Frey curve of a
coprime pair has good or multiplicative reduction everywhere.

Similarly, for `n ≠ 0` the difference of powers `a ^ n - b ^ n` is coprime to `a b`, being
`-b ^ n` modulo `a` and `a ^ n` modulo `b`: no prime divisor of `a ^ n - b ^ n` divides `a` or `b`.

## Main results

* `IsCoprime.mul_mul_add_sq_add_mul_add_sq`: if `a` and `b` are coprime, so are `a b (a + b)` and
  `a² + a b + b²`.
* `IsCoprime.mul_pow_sub_pow`: if `a` and `b` are coprime and `n ≠ 0`, then `a b` and
  `a ^ n - b ^ n` are coprime.
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

/-- **For coprime `a` and `b` and `n ≠ 0`, the elements `a b` and `a ^ n - b ^ n` are coprime**:
modulo `a` and `b` the difference is `-b ^ n` and `a ^ n`. -/
theorem IsCoprime.mul_pow_sub_pow (h : IsCoprime a b) {n : ℕ} (hn : n ≠ 0) :
    IsCoprime (a * b) (a ^ n - b ^ n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  refine IsCoprime.mul_left ?_ ?_
  · -- `a ^ n - b ^ n ≡ -b ^ n (mod a)`
    rw [show a ^ (m + 1) - b ^ (m + 1) = -b ^ (m + 1) + a * a ^ m by ring,
      IsCoprime.add_mul_left_right_iff, IsCoprime.neg_right_iff]
    exact h.pow_right
  · -- `a ^ n - b ^ n ≡ a ^ n (mod b)`
    rw [show a ^ (m + 1) - b ^ (m + 1) = a ^ (m + 1) - b * b ^ m by ring,
      IsCoprime.sub_mul_left_right_iff]
    exact h.symm.pow_right
