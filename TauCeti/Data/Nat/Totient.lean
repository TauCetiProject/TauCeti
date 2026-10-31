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
also lists the `n` with `φ(n) ≤ 2`, which are the orders of the roots of unity of degree at most
two over `ℚ`.

## Main results

* `TauCeti.Nat.totient_prime_pow_eq_one_iff`: for a prime `p`, `φ(p ^ k) = 1` iff `k = 0`, or
  `p = 2` and `k = 1`.
* `TauCeti.Nat.totient_le_two_iff`: `φ(n) ≤ 2` iff `n ∈ {0, 1, 2, 3, 4, 6}`.
-/

public section

namespace TauCeti.Nat

/-- For a prime `p`, the totient of `p ^ k` is one exactly when `k = 0`, or `p = 2` and `k = 1`. -/
theorem totient_prime_pow_eq_one_iff {p k : ℕ} (hp : p.Prime) :
    (p ^ k).totient = 1 ↔ k = 0 ∨ p = 2 ∧ k = 1 := by
  rw [Nat.totient_eq_one_iff, Nat.pow_eq_one, Nat.Prime.pow_eq_iff Nat.prime_two]
  simp [hp.ne_one]

/-- **The integers of totient at most two** are `0, 1, 2, 3, 4` and `6`. A prime factor `p ≥ 5`,
a factor `8` or `9`, or the factor `12` of `n` would contribute a divisor of `φ(n)` larger than
two. -/
theorem totient_le_two_iff {n : ℕ} :
    n.totient ≤ 2 ↔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 := by
  refine ⟨fun h => ?_, by rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;> decide⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl rfl
  -- Every divisor of `n` also has totient at most two.
  have hdvd : ∀ m, m ∣ n → m.totient ≤ 2 := fun m hm =>
    (Nat.le_of_dvd (Nat.totient_pos.2 hn) (Nat.totient_dvd_of_dvd hm)).trans h
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
  obtain ⟨b, k, hk3, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.pos.ne' 3 (by norm_num)
  -- The part `k` prime to `6` is `1`: a prime factor `p` of it has `p - 1 ≤ 2`.
  obtain rfl : k = 1 := by
    refine Nat.eq_one_iff_not_exists_prime_dvd.2 fun p hp hpk => ?_
    have h2 := hdvd p (Dvd.dvd.mul_left (Dvd.dvd.mul_left hpk _) _)
    rw [Nat.totient_prime hp] at h2
    have hp2 := hp.two_le
    obtain rfl | rfl : p = 2 ∨ p = 3 := by omega
    · exact Nat.not_even_iff_odd.2 hm (even_iff_two_dvd.2 (Dvd.dvd.mul_left hpk _))
    · exact hk3 hpk
  have ha : a ≤ 2 := by
    by_contra! ha
    exact absurd (hdvd 8 (Dvd.dvd.mul_right (Nat.pow_dvd_pow 2 ha) _)) (by decide)
  have hb : b ≤ 1 := by
    by_contra! hb
    exact absurd (hdvd 9 (Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.pow_dvd_pow 3 hb) _) _))
      (by decide)
  interval_cases a <;> interval_cases b <;> revert h <;> decide

end TauCeti.Nat
