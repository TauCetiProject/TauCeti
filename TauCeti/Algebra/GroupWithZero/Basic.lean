/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Int.ModEq

/-!
# Basic lemmas on monoids and groups with zero

In a reduced commutative monoid with zero, powers can be cancelled from annihilation relations:
if `a * b ^ k = 0`, then `a * b = 0`. In a group with zero, integer powers of an `n`-th root of
unity depend only on the exponent modulo `n`.

## Main results

* `TauCeti.mul_eq_zero_of_mul_pow_eq_zero`: in a reduced commutative monoid with zero,
  `a * b ^ k = 0` implies `a * b = 0`.
* `TauCeti.zpow_eq_zpow_of_modEq`: in a group with zero, if `η ^ n = 1` and `l ≡ m [ZMOD n]`,
  then `η ^ l = η ^ m`.
-/

public section

namespace TauCeti

/-- In a reduced commutative monoid with zero, if `a` kills `b ^ k` then `a` kills `b`. -/
theorem mul_eq_zero_of_mul_pow_eq_zero {M : Type*} [CommMonoidWithZero M] [IsReduced M]
    {a b : M} {k : ℕ} (h : a * b ^ k = 0) : a * b = 0 :=
  -- `(a * b) ^ (k + 1)` is a multiple of `a * b ^ k`.
  eq_zero_of_pow_eq_zero (n := k + 1) <| by
    rw [mul_pow, pow_succ a, pow_succ' b, mul_mul_mul_comm, h, mul_zero]

/-- In a group with zero, powers of an `n`-th root of unity with exponents congruent modulo `n`
agree. -/
theorem zpow_eq_zpow_of_modEq {G₀ : Type*} [GroupWithZero G₀] {n : ℕ} {η : G₀}
    (hη : η ^ n = 1) {l m : ℤ} (h : l ≡ m [ZMOD n]) : η ^ l = η ^ m := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [show l = m by simpa [Int.ModEq] using h]
  have h₀ : η ≠ 0 := ne_zero_pow hn (hη ▸ one_ne_zero)
  obtain ⟨c, hc⟩ := h.dvd
  rw [show m = l + n * c by omega, zpow_add₀ h₀, zpow_mul, zpow_natCast, hη, one_zpow, mul_one]

end TauCeti
