/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.IntervalCases

/-!
# Euler products and small values of the totient

Mathlib's `Nat.totient_eq_one_iff` says that `φ(n) = 1` exactly for `n = 1` and `n = 2`. This file
specialises it to prime powers: `φ(p ^ k) = 1` exactly when `k = 0`, or `p = 2` and `k = 1`. It
also lists the `n` with `φ(n) ≤ 2`, which are the orders of the roots of unity of degree at most
two over `ℚ`. It also writes Mathlib's product formula `Nat.totient_eq_mul_prod_factors` in
the reciprocal form used for Euler products over a field of characteristic zero.

## Main results

* `TauCeti.Nat.totient_prime_pow_eq_one_iff`: for a prime `p`, `φ(p ^ k) = 1` iff `k = 0`, or
  `p = 2` and `k = 1`.
* `TauCeti.Nat.totient_le_two_iff`: `φ(n) ≤ 2` iff `n ∈ {0, 1, 2, 3, 4, 6}`.
* `TauCeti.Nat.prod_inv_one_sub_inv_eq_div_totient`: for `n ≠ 0`,
  `∏_{p ∣ n} (1 - 1 / p)⁻¹ = n / φ(n)`.
* `TauCeti.Nat.pow_dvd_totient_pow_succ`: `ℓ ^ m ∣ φ(ℓ ^ (m + 1))` for every `ℓ`.
* `Nat.totient_mul_of_primeFactors_subset`: if `k` introduces no new prime factors into `n`,
  then `φ(nk) = k φ(n)`.
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

/-- The Euler factor of the primes of `n` is `n / φ(n)`: the reciprocal form of Mathlib's
`Nat.totient_eq_mul_prod_factors`, in any field of characteristic zero. -/
theorem prod_inv_one_sub_inv_eq_div_totient {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (hn : n ≠ 0) : ∏ p ∈ n.primeFactors, (1 - (p : K)⁻¹)⁻¹ = n / n.totient := by
  have h := congrArg (Rat.cast : ℚ → K) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  rw [Finset.prod_inv_distrib, h, div_mul_cancel_left₀ (Nat.cast_ne_zero.mpr hn)]

/-- `ℓ ^ m ∣ φ(ℓ ^ (m + 1))` for every `ℓ`, not only for primes as in Mathlib's
`Nat.totient_prime_pow_succ`. -/
theorem pow_dvd_totient_pow_succ (ℓ m : ℕ) : ℓ ^ m ∣ (ℓ ^ (m + 1)).totient := by
  induction m with
  | zero => exact one_dvd _
  | succ m ih =>
    rw [pow_succ' ℓ (m + 1), Nat.totient_mul_of_dvd (dvd_pow_self ℓ m.succ_ne_zero)]
    simpa only [pow_succ'] using mul_dvd_mul_left ℓ ih

end TauCeti.Nat

/-- Multiplying `n` by a factor `k` supported on the primes of `n` multiplies its totient by `k`.
The formula includes `n = 0` and `k = 0`. -/
theorem Nat.totient_mul_of_primeFactors_subset {n k : ℕ} (h : k.primeFactors ⊆ n.primeFactors) :
    (n * k).totient = k * n.totient := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hs : (n * k).primeFactors = n.primeFactors := by
    rw [Nat.primeFactors_mul hn hk, Finset.union_eq_left.mpr h]
  have hpos : 0 < ∏ p ∈ n.primeFactors, p :=
    Nat.pos_of_dvd_of_pos (Nat.prod_primeFactors_dvd n) (Nat.pos_of_ne_zero hn)
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc
    (n * k).totient * ∏ p ∈ n.primeFactors, p = (n * k) * ∏ p ∈ n.primeFactors, (p - 1) := by
      simpa only [hs] using Nat.totient_mul_prod_primeFactors (n * k)
    _ = k * (n * ∏ p ∈ n.primeFactors, (p - 1)) := by ac_rfl
    _ = (k * n.totient) * ∏ p ∈ n.primeFactors, p := by
      rw [mul_assoc k, Nat.totient_mul_prod_primeFactors]
