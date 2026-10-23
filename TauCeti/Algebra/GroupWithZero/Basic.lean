/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic

/-!
# Annihilators in reduced monoids with zero

In a reduced commutative monoid with zero, powers can be cancelled from annihilation relations:
if `a * b ^ k = 0`, then `a * b = 0`.

## Main results

* `TauCeti.mul_eq_zero_of_mul_pow_eq_zero`: in a reduced commutative monoid with zero,
  `a * b ^ k = 0` implies `a * b = 0`.
-/

public section

namespace TauCeti

/-- In a reduced commutative monoid with zero, if `a` kills `b ^ k` then `a` kills `b`. -/
theorem mul_eq_zero_of_mul_pow_eq_zero {M : Type*} [CommMonoidWithZero M] [IsReduced M]
    {a b : M} {k : ℕ} (h : a * b ^ k = 0) : a * b = 0 :=
  -- `(a * b) ^ (k + 1)` is a multiple of `a * b ^ k`.
  eq_zero_of_pow_eq_zero (n := k + 1) <| by
    rw [mul_pow, pow_succ a, pow_succ' b, mul_mul_mul_comm, h, mul_zero]

end TauCeti
