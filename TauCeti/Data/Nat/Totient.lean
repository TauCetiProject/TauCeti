/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.IntervalCases

/-!
# Small values of the totient

Mathlib's `Nat.totient_eq_one_iff` says that `φ(n) = 1` exactly for `n = 1` and `n = 2`. This file
specialises it to prime powers: `φ(p ^ k) = 1` exactly when `k = 0`, or `p = 2` and `k = 1`. It
also determines the next value: `φ(n) = 2` exactly for `n = 3, 4, 6`. These are the orders of the
roots of unity of degree exactly `2` over `ℚ`, which is what bounds the roots of unity in a
quadratic field.

## Main results

* `TauCeti.Nat.totient_prime_pow_eq_one_iff`: for a prime `p`, `φ(p ^ k) = 1` iff `k = 0`, or
  `p = 2` and `k = 1`.
* `TauCeti.Nat.totient_eq_two_iff`: `φ(n) = 2` iff `n` is `3`, `4` or `6`.
-/

public section

namespace TauCeti.Nat

/-- For a prime `p`, the totient of `p ^ k` is one exactly when `k = 0`, or `p = 2` and `k = 1`. -/
theorem totient_prime_pow_eq_one_iff {p k : ℕ} (hp : p.Prime) :
    (p ^ k).totient = 1 ↔ k = 0 ∨ p = 2 ∧ k = 1 := by
  rw [Nat.totient_eq_one_iff, Nat.pow_eq_one, Nat.Prime.pow_eq_iff Nat.prime_two]
  simp [hp.ne_one]

/-- **The totient is `2` exactly at `3`, `4` and `6`.** -/
theorem totient_eq_two_iff {n : ℕ} : n.totient = 2 ↔ n = 3 ∨ n = 4 ∨ n = 6 := by
  refine ⟨fun h => ?_, by rintro (rfl | rfl | rfl) <;> decide⟩
  -- Every prime power `p ^ (k + 1)` dividing `n` has totient `p ^ k * (p - 1)` dividing
  -- `φ(n) = 2`, which forces `p ^ (k + 1) ∣ 12`; so `n ∣ 12`, and `3`, `4`, `6` are the divisors
  -- of `12` with totient `2`.
  have h12 : n ∣ 12 := by
    refine (Nat.dvd_iff_prime_pow_dvd_dvd 12 n).mpr fun p k hp hpk => ?_
    rcases k with _ | k
    · simp
    have hle : p ^ k * (p - 1) ≤ 2 := by
      rw [← Nat.totient_prime_pow_succ hp, ← h]
      exact Nat.le_of_dvd (by omega) (Nat.totient_dvd_of_dvd hpk)
    have hp3 : p ≤ 3 := by
      have := le_trans (Nat.le_mul_of_pos_left (p - 1) (Nat.one_le_pow k p hp.pos)) hle
      omega
    interval_cases p
    · exact absurd hp Nat.not_prime_zero
    · exact absurd hp Nat.not_prime_one
    · have : k ≤ 1 := by
        by_contra! hk
        have := Nat.pow_le_pow_right two_pos hk
        omega
      interval_cases k <;> norm_num
    · have : k = 0 := by
        by_contra hk
        have := Nat.one_lt_pow hk (by norm_num : 1 < 3)
        omega
      subst this
      norm_num
  have := Nat.le_of_dvd (by norm_num) h12
  interval_cases n <;> first | omega | (revert h; decide)

end TauCeti.Nat
