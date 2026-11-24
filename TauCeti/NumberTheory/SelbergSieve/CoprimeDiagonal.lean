/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
public import TauCeti.NumberTheory.SelbergSieve.UpperBound

import TauCeti.NumberTheory.ArithmeticFunction.SquarefreeTotientSum
import TauCeti.NumberTheory.SelbergSieve.Bounds

/-!
# The Selberg diagonal sum with the primes of a modulus omitted

When a sieve omits the primes dividing a modulus `k` and sieves only by the primes not dividing
`k`, for instance to count primes in a progression modulo `k`, its Selberg diagonal sum contains
the coprime sum
`∑_{1 ≤ d < z, (d, k) = 1} μ(d)² / φ(d) ≥ (φ(k) / k) log z`
(`ArithmeticFunction.totient_div_mul_log_le_sum_moebius_sq_div_totient`), so the denominator of
Selberg's upper bound is bounded below uniformly in the modulus.

## Main results

* `BoundingSieve.totient_div_mul_log_le_diagonalMass`: a sieve containing every prime below `z`
  not dividing `k`, with densities at least `1 / p` there, has diagonal mass at least
  `(φ(k) / k) log z`.
* `BoundingSieve.log_le_sum_selbergTerms`: the case `k = 1`, for the inclusive normalizer.

## References

* D. R. Heath-Brown, *Lectures on sieves*, §3, proof of Corollary 3.1, display (3.2), and the
  progression bound (3.5)–(3.6).
-/

public section

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius Nat

namespace BoundingSieve

/-- If the sieving product contains every prime below `z` not dividing `k`, with density at
least `1 / p` at each of them, then the Selberg diagonal mass at `z` is at least
`(φ(k) / k) log z`. -/
theorem totient_div_mul_log_le_diagonalMass (s : BoundingSieve) (k : ℕ) {z : ℝ} (hz : 0 ≤ z)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬p ∣ k → p ∣ s.prodPrimes)
    (hnu : ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬p ∣ k → (p : ℝ)⁻¹ ≤ s.nu p) :
    φ k / k * Real.log z ≤ s.diagonalMass z := by
  refine (ArithmeticFunction.totient_div_mul_log_le_sum_moebius_sq_div_totient k hz).trans ?_
  rw [← sum_filter_of_ne (p := Squarefree) fun d _ h ↦ by
      by_contra hd
      simp [moebius_eq_zero_of_not_squarefree hd] at h,
    filter_filter, diagonalMass_def]
  -- A squarefree `d < z` coprime to `k` divides the sieving product, and there
  -- `1 / φ(d) ≤ selbergTerms d` by `inv_totient_le_selbergTerms`.
  have hdvd (d : ℕ) (hd : d ∈ (Ico 1 ⌈z⌉₊).filter fun d ↦ d.Coprime k ∧ Squarefree d) :
      d ∣ s.prodPrimes ∧ (d : ℝ) < z ∧
        ∀ p ∈ d.primeFactors, p.Prime ∧ (p : ℝ) < z ∧ ¬p ∣ k := by
    obtain ⟨hdI, hcop, hsq⟩ := mem_filter.mp hd
    have hdz : (d : ℝ) < z := Nat.lt_ceil.mp (mem_Ico.mp hdI).2
    have hp (p : ℕ) (hp : p ∈ d.primeFactors) : p.Prime ∧ (p : ℝ) < z ∧ ¬p ∣ k := by
      have hpp := Nat.prime_of_mem_primeFactors hp
      refine ⟨hpp, lt_of_le_of_lt (by exact_mod_cast Nat.le_of_mem_primeFactors hp) hdz,
        (hpp.coprime_iff_not_dvd.mp (hcop.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp)))⟩
    refine ⟨?_, hdz, hp⟩
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    exact prod_primes_dvd _ (fun p hp' ↦ (Nat.prime_of_mem_primeFactors hp').prime)
      fun p hp' ↦ hP p (hp p hp').1 (hp p hp').2.1 (hp p hp').2.2
  calc
    _ ≤ ∑ d ∈ (Ico 1 ⌈z⌉₊).filter fun d ↦ d.Coprime k ∧ Squarefree d, s.selbergTerms d := by
      refine sum_le_sum fun d hd ↦ ?_
      obtain ⟨hdP, -, hp⟩ := hdvd d hd
      rw [← Int.cast_pow, moebius_sq_eq_one_of_squarefree (mem_filter.mp hd).2.2, Int.cast_one,
        one_div]
      exact s.inv_totient_le_selbergTerms hdP fun p hpd ↦
        hnu p (hp p hpd).1 (hp p hpd).2.1 (hp p hpd).2.2
    _ ≤ _ := by
      refine sum_le_sum_of_subset_of_nonneg (fun d hd ↦ ?_) fun d hd _ ↦
        (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)).le
      obtain ⟨hdP, hdz, -⟩ := hdvd d hd
      exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdP, s.prodPrimes_ne_zero⟩, hdz⟩

/-- The finite Selberg normalizer is at least the logarithm of any nonnegative cutoff
whose primes strictly below it are in the sieve and have density at least the reciprocal
prime. -/
theorem log_le_sum_selbergTerms (s : BoundingSieve) (z : ℝ) (hz : 0 ≤ z)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) < z → p ∣ s.prodPrimes)
    (hnu : ∀ p : ℕ, p.Prime → (p : ℝ) < z → (p : ℝ)⁻¹ ≤ s.nu p) :
    Real.log z ≤
      ∑ d ∈ s.prodPrimes.divisors, if (d : ℝ) ≤ z then s.selbergTerms d else 0 := by
  have h := s.totient_div_mul_log_le_diagonalMass 1 hz (fun p hp hpz _ ↦ hP p hp hpz)
    fun p hp hpz _ ↦ hnu p hp hpz
  rw [Nat.totient_one, Nat.cast_one, div_one, one_mul, diagonalMass_def] at h
  rw [← sum_filter]
  exact h.trans <| sum_le_sum_of_subset_of_nonneg
    (fun d hd ↦ mem_filter.mpr ⟨(mem_filter.mp hd).1, (mem_filter.mp hd).2.le⟩)
    fun d hd _ ↦ (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)).le

end BoundingSieve
