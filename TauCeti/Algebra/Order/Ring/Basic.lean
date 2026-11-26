/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

/-!
# Inequalities in ordered rings

For `0 ≤ c` and `1 ≤ p` in a linearly ordered commutative ring, a lower bound `-c < a * p` gives
`-c < a`, since multiplying a negative `a` by `p ≥ 1` only decreases it. With `c` the dimension
of the space, this is the exponent step showing that a power `‖x‖ ^ a` which is locally `Lᵖ` is
also locally integrable.

Advancing the exponent of `(-1) ^ k * r` by `1` negates the product and therefore flips its strict
sign (`0 < (-1) ^ (k + 1) * r ↔ (-1) ^ k * r < 0`), which converts consecutive-order positivity
estimates for alternating remainders into opposite-sign bounds.

## Main results

* `TauCeti.neg_lt_of_neg_lt_mul`: `-c < a` from `-c < a * p` for `0 ≤ c` and `1 ≤ p`.
* `TauCeti.neg_one_pow_succ_mul_pos_iff`: `0 < (-1) ^ (k + 1) * r ↔ (-1) ^ k * r < 0`.
-/

public section

namespace TauCeti

/-- For `c ≥ 0` and `p ≥ 1`, the condition `a p > -c` implies `a > -c`, since multiplying a
negative `a` by `p` only decreases it. With `c` the dimension of the space: when `‖x‖ ^ a` is
locally `Lᵖ`, it is also locally integrable. -/
theorem neg_lt_of_neg_lt_mul {α : Type*} [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
    {a p c : α} (hc : 0 ≤ c) (hp : 1 ≤ p) (h : -c < a * p) : -c < a := by
  nlinarith

/-- Advancing the exponent of `(-1) ^ k * r` by `1` flips its strict sign:
`0 < (-1) ^ (k + 1) * r ↔ (-1) ^ k * r < 0`. -/
theorem neg_one_pow_succ_mul_pos_iff {R : Type*} [Ring R] [LT R] [AddLeftStrictMono R]
    {k : ℕ} {r : R} :
    0 < (-1 : R) ^ (k + 1) * r ↔ (-1 : R) ^ k * r < 0 := by
  rw [pow_succ', neg_one_mul, neg_mul, neg_pos]

end TauCeti
