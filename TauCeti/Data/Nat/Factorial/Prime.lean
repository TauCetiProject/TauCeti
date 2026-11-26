/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Prime powers dividing factorials

## Main results

* `Nat.Prime.sq_dvd_factorial_iff`: the square of a prime `p` divides `n!` if and only if
  `2 * p ≤ n`.
* `Nat.Prime.not_pow_dvd_factorial`: for any prime `p` and `k ≠ 0`, `p ^ k` does not divide `k!`.
* `Nat.Prime.dvd_of_pow_dvd_factorial_mul` and `Nat.Prime.intCast_dvd_of_pow_dvd_factorial_mul`:
  if `p ^ k` divides `k! * a` for `k ≠ 0`, then `p` divides `a` (over `ℕ` and `ℤ`).

`Nat.Prime.sq_dvd_factorial_iff` is the square analogue of Mathlib's `Nat.Prime.dvd_factorial`. In
particular `p ^ 2` does not divide `p!`, the order of the permutation group on `p` points, so it
does not divide the order of any of its subgroups. The `p ^ k` cancellation lemmas record that
`multiplicity p (k!) < k` forces at least one factor of `p` into `a` whenever `p ^ k ∣ k! * a`, as
used when propagating prime divisibility through divided-power identities `k! • x^{(k)} = x^k`.
-/

public section

namespace Nat.Prime

/-- The square of a prime `p` divides `n!` if and only if `2 * p ≤ n`. -/
theorem sq_dvd_factorial_iff {p n : ℕ} (hp : p.Prime) : p ^ 2 ∣ n ! ↔ 2 * p ≤ n := by
  have h2p : 2 * p ≤ p ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hp.two_le
  rcases lt_or_ge n (p ^ 2) with hn | hn
  · rw [hp.pow_dvd_factorial_iff (Nat.log_lt_of_lt_pow' two_ne_zero hn)]
    simp [Nat.le_div_iff_mul_le hp.pos]
  · exact iff_of_true (Nat.dvd_factorial (pow_pos hp.pos 2) hn) (h2p.trans hn)

/-- For any prime `p` and nonzero `k`, `p ^ k` does not divide `k!`. -/
theorem not_pow_dvd_factorial {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : ¬ p ^ k ∣ k ! := by
  let : Fact p.Prime := ⟨hp⟩
  rw [Nat.pow_dvd_iff_le_multiplicity hp.ne_one (Nat.factorial_ne_zero k)]
  exact not_le_of_gt (multiplicity_factorial_lt_of_ne_zero p hk)

/-- If `p ^ k` divides `k! * n` for a prime `p` and nonzero `k`, then `p` divides `n`. -/
theorem dvd_of_pow_dvd_factorial_mul {p k n : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    (h : p ^ k ∣ k ! * n) : p ∣ n := by
  by_contra hpn
  exact hp.not_pow_dvd_factorial hk
    (((hp.coprime_iff_not_dvd.mpr hpn).pow_left k).dvd_of_dvd_mul_right h)

/-- If `(p : ℤ) ^ k` divides `(k! : ℤ) * a` for a prime `p` and nonzero `k`, then `(p : ℤ)`
divides `a`. -/
theorem intCast_dvd_of_pow_dvd_factorial_mul {p k : ℕ} {a : ℤ} (hp : p.Prime) (hk : k ≠ 0)
    (h : (p : ℤ) ^ k ∣ (k ! : ℤ) * a) : (p : ℤ) ∣ a := by
  rw [Int.ofNat_dvd_left]
  refine hp.dvd_of_pow_dvd_factorial_mul hk ?_
  simpa only [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_natCast] using
    Int.natAbs_dvd_natAbs.mpr h

end Nat.Prime
