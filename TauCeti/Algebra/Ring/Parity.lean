/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Parity

/-!
# Parity of exponents of `-1`, of negated elements, and of nonzero elements

This file records the identity `1 - (-x)^{2n+1} = 1 + x^{2n+1}` in a ring, which turns a product
of factors `1 - (-q)^{2n+1}` into a product of factors `1 + q^{2n+1}`, and two sign cancellations
for powers of `-1` in a monoid with a distributive negation: an even summand of the exponent can be
dropped, and two equal powers of `-1` cancel. It also records that multiplying a sign `±1` by a
power of `-1` gives a sign.

Finally, it records that a nonzero even element keeps `2` nonzero: `Even.two_ne_zero_of_ne_zero`.
Combined with `Even.intCast`, a hypothesis `(n : R) ≠ 0` on an even integer `n` yields
`(2 : R) ≠ 0`.
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

/-- Multiplying a sign `μ = ±1` by a power of `-1` gives a sign. -/
theorem neg_one_pow_mul_eq_or {μ : α} (hμ : μ = 1 ∨ μ = -1) (n : ℕ) :
    (-1 : α) ^ n * μ = 1 ∨ (-1 : α) ^ n * μ = -1 := by
  rcases neg_one_pow_eq_or α n with h | h <;> rcases hμ with rfl | rfl <;> simp [h]

end NegOnePow

end TauCeti

/-- **A nonzero even element forces `2` to be nonzero**: it is `2` times something, so a vanishing
`2` would make it vanish too. -/
theorem Even.two_ne_zero_of_ne_zero {R : Type*} [NonAssocSemiring R] {x : R} (hx : Even x)
    (h : x ≠ 0) : (2 : R) ≠ 0 := by
  obtain ⟨y, rfl⟩ := hx
  exact fun h₂ ↦ h (by rw [← two_mul, h₂, zero_mul])

end
