/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Power comparisons in ordered monoids with zero

This file shows that a comparison `x ^ m ≤ y ^ n` of nonnegative elements of a linearly ordered
monoid with zero depends only on the ratio `m : n`.

## Main results

* `TauCeti.pow_le_pow_iff_of_mul_eq`: `x ^ m ≤ y ^ n ↔ x ^ m' ≤ y ^ n'` when the exponent pairs
  `(m, n)` and `(m', n')` are proportional.
-/

public section

namespace TauCeti

/-- In a linearly ordered monoid with zero, raising both sides of `x ^ m ≤ y ^ n` to a nonzero
power does not change it, so for nonnegative `x` and `y` the comparison depends only on the ratio
of the exponents: if `(m, n)` and `(m', n')` are proportional, with
`m * c = m' * c'` and `n * c = n' * c'` for nonzero `c` and `c'`, then
`x ^ m ≤ y ^ n ↔ x ^ m' ≤ y ^ n'`. -/
theorem pow_le_pow_iff_of_mul_eq {M₀ : Type*} [MonoidWithZero M₀] [LinearOrder M₀]
    [ZeroLEOneClass M₀] [PosMulStrictMono M₀] [MulPosMono M₀] {x y : M₀} (hx : 0 ≤ x) (hy : 0 ≤ y)
    {m n m' n' c c' : ℕ} (hc : c ≠ 0) (hc' : c' ≠ 0) (hm : m * c = m' * c')
    (hn : n * c = n' * c') : x ^ m ≤ y ^ n ↔ x ^ m' ≤ y ^ n' := by
  calc x ^ m ≤ y ^ n ↔ (x ^ m) ^ c ≤ (y ^ n) ^ c :=
        (pow_le_pow_iff_left₀ (pow_nonneg hx _) (pow_nonneg hy _) hc).symm
    _ ↔ (x ^ m') ^ c' ≤ (y ^ n') ^ c' := by simp only [← pow_mul, hm, hn]
    _ ↔ x ^ m' ≤ y ^ n' := pow_le_pow_iff_left₀ (pow_nonneg hx _) (pow_nonneg hy _) hc'

end TauCeti
