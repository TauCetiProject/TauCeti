/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Power comparisons in ordered monoids with zero

This file collects power-comparison lemmas for nonnegative elements of a linearly ordered monoid
with zero:

* a comparison `x ^ m ≤ y ^ n` depends only on the ratio `m : n`
  (`TauCeti.pow_le_pow_iff_of_mul_eq`);
* replacing the base `c ≥ 0` by `max 1 c ≥ 1` allows raising the exponent (`c ^ m ≤ max 1 c ^ n`
  for `m ≤ n`) and re-basing shifted or rescaled geometric bounds (`c ^ m ≤ (max 1 c ^ k) ^ n`
  for `m ≤ k * n`).

## Main results

* `TauCeti.pow_le_pow_iff_of_mul_eq`: `x ^ m ≤ y ^ n ↔ x ^ m' ≤ y ^ n'` when the exponent pairs
  `(m, n)` and `(m', n')` are proportional.
* `TauCeti.pow_le_max_one_pow`: `c ^ m ≤ max 1 c ^ n` for `0 ≤ c` and `m ≤ n`.
* `TauCeti.pow_le_max_one_pow_pow`: `c ^ m ≤ (max 1 c ^ k) ^ n` for `0 ≤ c` and `m ≤ k * n`.
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

/-- For a nonnegative element `c` of a linearly ordered monoid with zero and exponents `m ≤ n`,
`c ^ m ≤ max 1 c ^ n`. -/
theorem pow_le_max_one_pow {M₀ : Type*} [MonoidWithZero M₀] [LinearOrder M₀]
    [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀]
    {c : M₀} (hc : 0 ≤ c) {m n : ℕ} (hmn : m ≤ n) :
    c ^ m ≤ max 1 c ^ n :=
  (pow_le_pow_left₀ hc (le_max_right 1 c) m).trans (pow_le_pow_right₀ (le_max_left 1 c) hmn)

/-- For a nonnegative element `c` of a linearly ordered monoid with zero and `m ≤ k * n`,
`c ^ m ≤ (max 1 c ^ k) ^ n`. This re-bases shifted or rescaled geometric bounds such as
`c ^ (n + 2) ≤ (max 1 c ^ 2) ^ (n + 1)` back to exponent `n`. -/
theorem pow_le_max_one_pow_pow {M₀ : Type*} [MonoidWithZero M₀] [LinearOrder M₀]
    [ZeroLEOneClass M₀] [PosMulMono M₀] [MulPosMono M₀]
    {c : M₀} (hc : 0 ≤ c) {k m n : ℕ} (h : m ≤ k * n) :
    c ^ m ≤ (max 1 c ^ k) ^ n := by
  rw [← pow_mul]
  exact pow_le_max_one_pow hc h

end TauCeti
