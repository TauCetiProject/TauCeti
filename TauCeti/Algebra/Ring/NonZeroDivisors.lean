/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.NonZeroDivisors
public import TauCeti.Algebra.GroupWithZero.NonZeroDivisors

/-!
# Divisibility of powers by nonzerodivisors in commutative rings

In a commutative ring `R`, if `w ^ n` (`n ≠ 0`) is a nonzerodivisor and divisibility by `w ^ n` is
detected on `n`-th powers, then divisibility by `w` is also detected on `n`-th powers: multiplying
`w ^ n ∣ z ^ n` by `(w ^ n) ^ (n - 1)` gives `(w ^ n) ^ n ∣ (z * w ^ (n - 1)) ^ n`, hence
`w ^ n ∣ z * w ^ (n - 1)`, and cancelling the nonzerodivisor `w ^ (n - 1)` gives `w ∣ z`.

## Main results

* `TauCeti.dvd_of_pow_dvd_pow`: if `w ^ n ∈ R⁰` (`n ≠ 0`) and `(w ^ n) ^ n ∣ u ^ n → w ^ n ∣ u`
  for all `u`, then `w ^ n ∣ z ^ n → w ∣ z`.
-/

public section

open scoped nonZeroDivisors

namespace TauCeti

/-- In a commutative ring `R`, if `w ^ n` (`n ≠ 0`) is a nonzerodivisor and divisibility by `w ^ n`
is detected on `n`-th powers, then divisibility by `w` is also detected on `n`-th powers. -/
theorem dvd_of_pow_dvd_pow {R : Type*} [CommRing R] {w z : R} {n : ℕ} (hn : n ≠ 0)
    (hw : w ^ n ∈ R⁰) (hinj : ∀ u : R, (w ^ n) ^ n ∣ u ^ n → w ^ n ∣ u) (hz : w ^ n ∣ z ^ n) :
    w ∣ z := by
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
  have hd : w * w ^ (n - 1) ∣ z * w ^ (n - 1) := by
    have hpow : w ^ n = w * w ^ (n - 1) := by
      conv_lhs => rw [← hn1]
      exact pow_succ' w (n - 1)
    rw [← hpow]
    refine hinj _ ?_
    have hlhs : w ^ n * (w ^ n) ^ (n - 1) = (w ^ n) ^ n :=
      (pow_succ' (w ^ n) (n - 1)).symm.trans (by rw [hn1])
    have hrhs : z ^ n * (w ^ n) ^ (n - 1) = (z * w ^ (n - 1)) ^ n := by
      rw [← pow_mul, mul_comm n (n - 1), pow_mul, mul_pow]
    rw [← hlhs, ← hrhs]
    exact mul_dvd_mul_right hz _
  exact (dvd_cancel_right_mem_nonZeroDivisors
    (pow_mem ((pow_mem_nonZeroDivisors_iff hn).mp hw) (n - 1))).mp hd

end TauCeti

end
