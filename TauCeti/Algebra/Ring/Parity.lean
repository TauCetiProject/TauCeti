/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Parity

/-!
# Parity of exponents of `-1` and of negated elements

This file records the identity `1 - (-x)^{2n+1} = 1 + x^{2n+1}` in a ring, which turns a product
of factors `1 - (-q)^{2n+1}` into a product of factors `1 + q^{2n+1}`, and two sign cancellations
for powers of `-1` in a monoid with a distributive negation: an even summand of the exponent can be
dropped, and two equal powers of `-1` cancel.
-/

public section

namespace TauCeti

/-- `1 - (-x)^{2n+1} = 1 + x^{2n+1}`. -/
theorem one_sub_neg_pow_odd {R : Type*} [Ring R] (x : R) (n : ℕ) :
    1 - (-x) ^ (2 * n + 1) = 1 + x ^ (2 * n + 1) := by
  rw [Odd.neg_pow (by simp), sub_neg_eq_add]

section NegOnePow

variable {α : Type*} [Monoid α] [HasDistribNeg α]

/-- An even summand of the exponent of `-1` can be dropped: `(-1)^{a + 2b} = (-1)^a`. -/
@[simp]
theorem neg_one_pow_add_two_mul (a b : ℕ) : (-1 : α) ^ (a + 2 * b) = (-1) ^ a := by
  rw [pow_add, (even_two_mul b).neg_one_pow, mul_one]

/-- Two equal powers of `-1` cancel: `(-1)^a * ((-1)^a * x) = x`. -/
@[simp]
theorem neg_one_pow_mul_neg_one_pow_mul (a : ℕ) (x : α) :
    (-1 : α) ^ a * ((-1) ^ a * x) = x := by
  rw [← mul_assoc, ← pow_add, ← two_mul, (even_two_mul a).neg_one_pow, one_mul]

end NegOnePow

end TauCeti

end
