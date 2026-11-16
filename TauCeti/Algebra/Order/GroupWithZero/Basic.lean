/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs

/-!
# Strict upper bounds for products in ordered magmas with zero

This file records the strict-inequality counterpart to Mathlib's
`mul_le_of_mul_le_of_nonneg_left` and `mul_lt_of_mul_lt_of_nonneg_left`: when `0 ≤ a`, `a * b ≤ c`,
`d < b`, and `0 < c`, we have `a * d < c`. The positivity of `c` handles the `a = 0` branch,
where `0 * d = 0 < c`, while `PosMulStrictMono` gives `a * d < a * b ≤ c` for `0 < a`.

## Main results

* `TauCeti.mul_lt_of_mul_le_of_nonneg_left`: `a * d < c` from `a * b ≤ c`, `d < b`, `0 ≤ a`, and
  `0 < c`.
-/

public section

namespace TauCeti

/-- If `a * b ≤ c`, `d < b`, `0 ≤ a`, and `0 < c`, then `a * d < c`. -/
theorem mul_lt_of_mul_le_of_nonneg_left {α : Type*} [MulZeroClass α] [PartialOrder α]
    [PosMulStrictMono α] {a b c d : α} (h : a * b ≤ c) (hlt : d < b) (a0 : 0 ≤ a) (c0 : 0 < c) :
    a * d < c := by
  obtain rfl | ha := a0.eq_or_lt
  · simpa only [zero_mul] using c0
  · exact (mul_lt_mul_of_pos_left hlt ha).trans_le h

end TauCeti
