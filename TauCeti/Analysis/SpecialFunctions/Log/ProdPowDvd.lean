/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Logarithms of prime-power divisors of an integer

If `∏ p ∈ P, p ^ e p` divides a nonzero integer `z`, then the divisor is at most `|z|`, and taking
logarithms gives `∑ p ∈ P, e p * log p ≤ log |z|`.

## Main results

* `Int.sum_mul_log_le_log_abs`: `∑ p ∈ P, e p * log p ≤ log |z|` when `∏ p ∈ P, p ^ e p ∣ z ≠ 0`.
* `Int.sum_mul_log_le_log_abs_of_prime`, `Nat.sum_mul_log_le_log_of_prime`: pointwise prime-power
  divisibility versions for an arbitrary finite set of primes `P`.
-/

public section

/-- If `∏ p ∈ P, p ^ e p` divides a nonzero integer `z`, then `∑ p ∈ P, e p * log p ≤ log |z|`. -/
theorem Int.sum_mul_log_le_log_abs {P : Finset ℕ} (e : ℕ → ℕ) {z : ℤ} (hz : z ≠ 0)
    (h : ∏ p ∈ P, (p : ℤ) ^ e p ∣ z) :
    ∑ p ∈ P, (e p : ℝ) * Real.log p ≤ Real.log |(z : ℝ)| := by
  have hd : ∏ p ∈ P, (p : ℤ) ^ e p ≠ 0 := ne_zero_of_dvd_ne_zero hz h
  have hle : ∏ p ∈ P, (p : ℝ) ^ e p ≤ |(z : ℝ)| := by
    exact_mod_cast Int.le_of_dvd (abs_pos.2 hz) ((dvd_abs _ _).2 h)
  have hpos : 0 < ∏ p ∈ P, (p : ℝ) ^ e p :=
    (Finset.prod_nonneg fun _ _ => by positivity).lt_of_ne' (by exact_mod_cast hd)
  calc ∑ p ∈ P, (e p : ℝ) * Real.log p = Real.log (∏ p ∈ P, (p : ℝ) ^ e p) := by
        rw [Real.log_prod fun p hp => (Finset.prod_ne_zero_iff.1 hpos.ne' p hp)]
        simp [Real.log_pow]
    _ ≤ Real.log |(z : ℝ)| := Real.log_le_log hpos hle

/-- If `P` is a finite set of primes and `(p : ℤ) ^ e p` divides a nonzero integer `z` for each
`p ∈ P`, then `∑ p ∈ P, e p * log p ≤ log |z|`. -/
theorem Int.sum_mul_log_le_log_abs_of_prime {P : Finset ℕ} (e : ℕ → ℕ) {z : ℤ} (hz : z ≠ 0)
    (hP : ∀ p ∈ P, p.Prime) (hdvd : ∀ p ∈ P, (p : ℤ) ^ e p ∣ z) :
    ∑ p ∈ P, (e p : ℝ) * Real.log p ≤ Real.log |(z : ℝ)| := by
  refine Int.sum_mul_log_le_log_abs e hz
    (Finset.prod_dvd_of_coprime (fun p hp p' hp' hne => ?_) hdvd)
  have hp_pr := hP p hp
  have hp'_pr := hP p' hp'
  simpa only [Nat.cast_pow] using ((hp_pr.coprime_iff_not_dvd.mpr fun h =>
    hne ((Nat.prime_dvd_prime_iff_eq hp_pr hp'_pr).mp h)).pow _ _).isCoprime

/-- If `P` is a finite set of primes and `p ^ e p` divides a positive natural number `n` for each
`p ∈ P`, then `∑ p ∈ P, e p * log p ≤ log n`. -/
theorem Nat.sum_mul_log_le_log_of_prime {P : Finset ℕ} (e : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    (hP : ∀ p ∈ P, p.Prime) (hdvd : ∀ p ∈ P, p ^ e p ∣ n) :
    ∑ p ∈ P, (e p : ℝ) * Real.log p ≤ Real.log (n : ℝ) := by
  have hle := Int.sum_mul_log_le_log_abs_of_prime e (Int.natCast_ne_zero.mpr hn.ne') hP
    fun p hp => Int.ofNat_dvd.mpr (hdvd p hp)
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  rwa [Int.cast_natCast, abs_of_pos hn_real] at hle
