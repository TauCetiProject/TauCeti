/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.IntervalCases

/-!
# Integer factorisations of `2`

A nonnegative (resp. nonpositive) integer whose product with another integer is `2` is `1` or `2`
(resp. `-1` or `-2`), and the cofactor is the other one.

## Main results

* `Int.eq_one_and_eq_two_or_of_mul_eq_two`: the two ordered factorisations of `2` by a nonnegative
  first factor.
* `Int.eq_neg_one_and_eq_neg_two_or_of_mul_eq_two`: the same for a nonpositive first factor.
-/

public section

namespace Int

/-- **A nonnegative integer factor of `2` is `1` or `2`**: if `a * b = 2` and `0 ≤ a`, then
`(a, b)` is `(1, 2)` or `(2, 1)`. -/
lemma eq_one_and_eq_two_or_of_mul_eq_two {a b : ℤ} (ha : 0 ≤ a) (hab : a * b = 2) :
    (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
  have hdvd : a ∣ 2 := ⟨b, hab.symm⟩
  have hle : a ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
  interval_cases a <;> omega

/-- **Two nonpositive integers whose product is `2` are `-1` and `-2`**, in one order or the other:
the two entries of a double edge, whose orientation this splits into its two cases. -/
lemma eq_neg_one_and_eq_neg_two_or_of_mul_eq_two {x y : ℤ} (hx : x ≤ 0) (hxy : x * y = 2) :
    (x = -1 ∧ y = -2) ∨ (x = -2 ∧ y = -1) := by
  have := eq_one_and_eq_two_or_of_mul_eq_two (neg_nonneg.2 hx) (by rwa [neg_mul_neg])
  omega

end Int
