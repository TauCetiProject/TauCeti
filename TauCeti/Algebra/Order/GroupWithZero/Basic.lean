/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Basic order inequalities for multiplication with zero

This file records elementary order inequalities in types with a zero, multiplication, and
`PosMulStrictMono`, as well as linearly ordered commutative groups with zero.

## Main results

* `TauCeti.mul_lt_of_lt_of_mul_le`: `a * b < d` from `0 ≤ a`, `0 < d`, `b < c`, and `a * c ≤ d`,
  covering both `a = 0` and `0 < a`.
* `TauCeti.le_div_mul_of_le`: `c ≤ c / a * b` from `0 ≤ c`, `0 < a`, and `a ≤ b`.
-/

public section

namespace TauCeti

/-- If `0 ≤ a`, `0 < d`, `b < c`, and `a * c ≤ d`, then `a * b < d`, including the case
`a = 0`. -/
theorem mul_lt_of_lt_of_mul_le {α : Type*} [MulZeroClass α] [PartialOrder α] [PosMulStrictMono α]
    {a b c d : α} (ha : 0 ≤ a) (hd : 0 < d) (hbc : b < c) (h : a * c ≤ d) : a * b < d := by
  rcases ha.eq_or_lt with rfl | ha'
  · simpa using hd
  · exact (mul_lt_mul_of_pos_left hbc ha').trans_le h

/-- Rescaling a nonnegative bound across a positive threshold `a ≤ b`: `c ≤ c / a * b`. -/
theorem le_div_mul_of_le {α : Type*} [CommGroupWithZero α] [LinearOrder α]
    [PosMulMono α] [PosMulReflectLT α] {a b c : α}
    (hc : 0 ≤ c) (ha : 0 < a) (hab : a ≤ b) : c ≤ c / a * b :=
  (div_mul_cancel₀ c ha.ne').symm.trans_le (mul_le_mul_of_nonneg_left hab (div_nonneg hc ha.le))

end TauCeti
