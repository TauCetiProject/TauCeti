/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Factorials vanishing in a semiring and falling-factorial casts

If a positive natural number `m` vanishes in a semiring `R`, then so does the factorial of every
natural number `k ≥ m`, since `m ∣ k !`.

In a commutative semiring `R`, factoring `y ^ n` out of `(k.descFactorial n : R) * y ^ k` gives
`y ^ n * ((k.descFactorial n : R) * y ^ (k - n))` for all `k` and `n`
(`Nat.cast_descFactorial_mul_pow`), since `k.descFactorial n = 0` when `k < n`.

## Main results

* `Nat.cast_factorial_eq_zero_of_le`: `(m : R) = 0` with `0 < m ≤ k` gives `(k ! : R) = 0`.
* `Nat.cast_descFactorial_mul_pow`:
  `(k.descFactorial n : R) * y ^ k = y ^ n * ((k.descFactorial n : R) * y ^ (k - n))`.
-/

public section

namespace Nat

variable {R : Type*} [Semiring R]

/-- If `m` is positive and vanishes in `R`, so does the factorial of every `k ≥ m`. -/
theorem cast_factorial_eq_zero_of_le {m k : ℕ} (hm : 0 < m) (hmR : (m : R) = 0) (hk : m ≤ k) :
    (k.factorial : R) = 0 := by
  simpa only [hmR, zero_dvd_iff] using
    (Nat.cast_dvd_cast (Nat.dvd_factorial hm hk) : (m : R) ∣ (k.factorial : R))

/-- In a commutative semiring `S`, factoring `y ^ n` out of `(k.descFactorial n : S) * y ^ k`
gives `y ^ n * ((k.descFactorial n : S) * y ^ (k - n))`, even when `k < n` (as
`k.descFactorial n = 0`). -/
theorem cast_descFactorial_mul_pow {S : Type*} [CommSemiring S] (y : S) (k n : ℕ) :
    (k.descFactorial n : S) * y ^ k = y ^ n * ((k.descFactorial n : S) * y ^ (k - n)) := by
  rcases lt_or_ge k n with hkn | hnk
  · simp [Nat.descFactorial_eq_zero_iff_lt.mpr hkn]
  · rw [mul_left_comm, ← pow_add, Nat.add_sub_of_le hnk]

end Nat
