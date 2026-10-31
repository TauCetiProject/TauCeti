/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Int

/-!
# Sign factors of integers

The factor `if x < 0 then -1 else 1` is the sign of a nonzero integer `x`, and its variant
`if p ∧ x < 0 then -1 else 1`, which switches the sign on only under a side condition `p`, is
multiplicative in `x` over nonzero factors. Such factors occur in the Kronecker symbol, whose value
at the denominator `-1` is the sign factor of the numerator.

## Main statements

* `Int.ite_lt_zero_eq_sign`: for `x ≠ 0`, `(if x < 0 then -1 else 1) = x.sign`.
* `Int.ite_and_mul_lt_zero`: the factor `if p ∧ x < 0 then -1 else 1` is multiplicative
  in `x` over nonzero factors.
-/

public section

namespace Int

/-- For `x ≠ 0`, the sign factor `if x < 0 then -1 else 1` is the sign of `x`. -/
theorem ite_lt_zero_eq_sign {x : ℤ} (hx : x ≠ 0) :
    (if x < 0 then -1 else 1 : ℤ) = x.sign := by
  rcases hx.lt_or_gt with h | h
  · rw [Int.sign_eq_neg_one_of_neg h, ite_eq_left h]
  · rw [Int.sign_eq_one_of_pos h, ite_eq_right h.not_gt]

/-- The sign factor `if p ∧ x < 0 then -1 else 1` is multiplicative in `x` over nonzero factors. -/
theorem ite_and_mul_lt_zero {p : Prop} [Decidable p] {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (if p ∧ x * y < 0 then -1 else 1 : ℤ) =
      (if p ∧ x < 0 then -1 else 1) * (if p ∧ y < 0 then -1 else 1) := by
  rcases hx.lt_or_gt with hx | hx <;> rcases hy.lt_or_gt with hy | hy <;> by_cases hp : p <;>
    simp [hp, hx, hy, hx.not_gt, hy.not_gt, mul_neg_iff]

end Int

end
