/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith

/-!
# Reciprocal inequalities in ordered fields

This file records a bound on a sum of two reciprocals in a linearly ordered field. It turns a lower
bound on a reciprocal sum `1 / b + 1 / c` with `b ≤ c` into an upper bound on the smaller
denominator `b`; the classifications of sorted triangle-group signatures use it to bound their
second parameter.

## Main results

* `TauCeti.one_div_add_one_div_le_two_div`: for `0 < b ≤ c`, the sum `1 / b + 1 / c` is at most
  `2 / b`.
-/

public section

namespace TauCeti

/-- For `0 < b ≤ c`, the sum `1 / b + 1 / c` is at most `2 / b`. -/
theorem one_div_add_one_div_le_two_div {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] {b c : α} (hb : 0 < b) (hbc : b ≤ c) :
    1 / b + 1 / c ≤ 2 / b := by
  have hcb : 1 / c ≤ 1 / b := one_div_le_one_div_of_le hb hbc
  rw [div_eq_mul_one_div (2 : α)]
  linarith

end TauCeti
