/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Absolute values of elements of finite order

An absolute value with values in a linearly ordered ring takes the value `1` at every element of
finite multiplicative order, for instance at every root of unity of a field: if `x ^ n = 1` with
`n ≠ 0`, then `abv x ^ n = 1` with `abv x ≥ 0`, so `abv x = 1`.
-/

public section

namespace AbsoluteValue

variable {R S : Type*} [Semiring R] [Nontrivial R] [Ring S] [LinearOrder S]
  [IsStrictOrderedRing S]

/-- An absolute value takes the value `1` at every element of finite order. -/
@[simp]
theorem map_eq_one_of_isOfFinOrder (abv : AbsoluteValue R S) {x : R} (hx : IsOfFinOrder x) :
    abv x = 1 := by
  obtain ⟨n, hn, hxn⟩ := hx.exists_pow_eq_one
  rw [← pow_eq_one_iff_of_nonneg (abv.nonneg x) hn.ne', ← abv.map_pow, hxn, abv.map_one]

end AbsoluteValue
