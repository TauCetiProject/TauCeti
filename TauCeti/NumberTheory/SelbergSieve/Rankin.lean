/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.SelbergSieve
import TauCeti.NumberTheory.SelbergSieve.Legendre

/-!
# Rankin's trick for sieve densities

For a Mathlib bounding sieve with squarefree sifting product `P` and multiplicative density `ν`,
the density moment `∑_{d ∣ P} ν(d) d ^ a` is the finite Euler product `∏_{p ∣ P} (1 + ν(p) p ^ a)`
for every real exponent `a`. Rankin's trick compares an indicator of `d ≤ x` or of `x < d` with a
power of `d / x` and so bounds truncated density sums by such an Euler product. Together with
Legendre's identity this gives an estimate for the sifted sum in which the remainders are only
controlled up to a cutoff.

## Main results

* `BoundingSieve.sum_nu_mul_rpow_eq_prod`:
  `∑_{d ∣ P} ν(d) d ^ a = ∏_{p ∣ P} (1 + ν(p) p ^ a)`.
* `BoundingSieve.sum_filter_le_mul_nu_le_rpow_mul_prod`: for `0 ≤ x` and `0 ≤ σ`,
  `∑_{d ∣ P, d ≤ x} d ν(d) ≤ x ^ σ ∏_{p ∣ P} (1 + ν(p) p ^ (1 - σ))`.
* `BoundingSieve.sum_filter_lt_nu_le_rpow_neg_mul_prod`: for `0 < x` and `0 ≤ a`,
  `∑_{d ∣ P, x < d} ν(d) ≤ x ^ (-a) ∏_{p ∣ P} (1 + ν(p) p ^ a)`.
* `BoundingSieve.abs_siftedSum_sub_totalMass_mul_prod_le_rpow_mul_prod`: if `0 ≤ X ≤ M x`,
  `|R_d| ≤ c d ν(d)` for the divisors `d ≤ x` of `P` and `A_d = 0` for the divisors `d > x`, then
  `|S - X ∏_{p ∣ P} (1 - ν(p))| ≤ (c + M) x ^ σ ∏_{p ∣ P} (1 + ν(p) p ^ (1 - σ))` for
  `0 ≤ σ ≤ 1`.

The mass bound and the vanishing of the divisor sums beyond the cutoff are hypotheses of the last
statement. They are properties of a particular sieve problem and do not follow from the sieve
structure.

## References

* K. S. Kedlaya, *Notes on analytic number theory*, Chapter 11: Rankin's trick is Lemma 11.5 of
  §11.3, and §11.4 states Lemmas 11.7 and 11.8 and Theorem 11.9, with proofs left to Exercises
  11.6.1 and 11.6.3. There the density is `ω(d) / d`, so that `d ν(d) = ω(d)`, and the estimates
  are asymptotic under a dimension hypothesis. This file proves the finite inequalities, with
  explicit Euler products, from which those estimates follow.
-/

public section

open Finset Nat ArithmeticFunction

namespace BoundingSieve

variable (s : BoundingSieve) {x σ a c M : ℝ}

/-- The density moment of exponent `a` over the divisors of the sifting product is a finite Euler
product: `∑_{d ∣ P} ν(d) d ^ a = ∏_{p ∣ P} (1 + ν(p) p ^ a)`. -/
theorem sum_nu_mul_rpow_eq_prod (a : ℝ) :
    ∑ d ∈ s.prodPrimes.divisors, s.nu d * (d : ℝ) ^ a =
      ∏ p ∈ s.prodPrimes.primeFactors, (1 + s.nu p * (p : ℝ) ^ a) := by
  let h : ArithmeticFunction ℝ := ⟨fun n ↦ if n = 0 then 0 else (n : ℝ) ^ a, by simp⟩
  have hh (n : ℕ) (hn : n ≠ 0) : h n = (n : ℝ) ^ a := ite_eq_right hn
  have hmul : h.IsMultiplicative := by
    refine ⟨by simp [h], fun {m n} _ ↦ ?_⟩
    rcases eq_or_ne m 0 with rfl | hm
    · simp [h]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [h]
    simp [h, hm, hn, Real.mul_rpow]
  calc ∑ d ∈ s.prodPrimes.divisors, s.nu d * (d : ℝ) ^ a
      = ∑ d ∈ s.prodPrimes.divisors, (s.nu.pmul h) d :=
        sum_congr rfl fun d hd ↦ by rw [pmul_apply, hh d (pos_of_mem_divisors hd).ne']
    _ = ∏ p ∈ s.prodPrimes.primeFactors, (1 + (s.nu.pmul h) p) :=
        ((s.nu_mult.pmul hmul).prodPrimeFactors_one_add_of_squarefree
          s.prodPrimes_squarefree).symm
    _ = ∏ p ∈ s.prodPrimes.primeFactors, (1 + s.nu p * (p : ℝ) ^ a) :=
        prod_congr rfl fun p hp ↦ by
          rw [pmul_apply, hh p (prime_of_mem_primeFactors hp).ne_zero]

/-- **Rankin's bound for a weighted density sum up to a cutoff.** For `0 ≤ x` and `0 ≤ σ`,
`∑_{d ∣ P, d ≤ x} d ν(d) ≤ x ^ σ ∏_{p ∣ P} (1 + ν(p) p ^ (1 - σ))`. The cutoff is inclusive. -/
theorem sum_filter_le_mul_nu_le_rpow_mul_prod (hx : 0 ≤ x) (hσ : 0 ≤ σ) :
    ∑ d ∈ s.prodPrimes.divisors.filter fun d : ℕ ↦ (d : ℝ) ≤ x, (d : ℝ) * s.nu d ≤
      x ^ σ * ∏ p ∈ s.prodPrimes.primeFactors, (1 + s.nu p * (p : ℝ) ^ (1 - σ)) := by
  rw [← s.sum_nu_mul_rpow_eq_prod, mul_sum]
  have hterm (d : ℕ) (hd : d ∈ s.prodPrimes.divisors) :
      0 ≤ s.nu d * (d : ℝ) ^ (1 - σ) :=
    mul_nonneg (s.nu_pos_of_dvd_prodPrimes (dvd_of_mem_divisors hd)).le
      (Real.rpow_nonneg d.cast_nonneg _)
  refine (sum_le_sum fun d hd ↦ ?_).trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    fun d hd _ ↦ mul_nonneg (Real.rpow_nonneg hx σ) (hterm d hd))
  obtain ⟨hd, hdx⟩ := mem_filter.1 hd
  have hd0 : (0 : ℝ) < d := mod_cast pos_of_mem_divisors hd
  calc (d : ℝ) * s.nu d = (d : ℝ) ^ σ * (s.nu d * (d : ℝ) ^ (1 - σ)) := by
        rw [mul_left_comm, ← Real.rpow_add hd0, add_sub_cancel, Real.rpow_one, mul_comm]
    _ ≤ x ^ σ * (s.nu d * (d : ℝ) ^ (1 - σ)) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd0.le hdx hσ) (hterm d hd)

/-- **Rankin's bound for the tail of a density sum.** For `0 < x` and `0 ≤ a`,
`∑_{d ∣ P, x < d} ν(d) ≤ x ^ (-a) ∏_{p ∣ P} (1 + ν(p) p ^ a)`. The tail is strict. -/
theorem sum_filter_lt_nu_le_rpow_neg_mul_prod (hx : 0 < x) (ha : 0 ≤ a) :
    ∑ d ∈ s.prodPrimes.divisors.filter fun d : ℕ ↦ x < (d : ℝ), s.nu d ≤
      x ^ (-a) * ∏ p ∈ s.prodPrimes.primeFactors, (1 + s.nu p * (p : ℝ) ^ a) := by
  rw [← s.sum_nu_mul_rpow_eq_prod, mul_sum]
  have hν (d : ℕ) (hd : d ∈ s.prodPrimes.divisors) : 0 ≤ s.nu d :=
    (s.nu_pos_of_dvd_prodPrimes (dvd_of_mem_divisors hd)).le
  refine (sum_le_sum fun d hd ↦ ?_).trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    fun d hd _ ↦ mul_nonneg (Real.rpow_nonneg hx.le _)
      (mul_nonneg (hν d hd) (Real.rpow_nonneg d.cast_nonneg _)))
  obtain ⟨hd, hdx⟩ := mem_filter.1 hd
  have hd0 : (0 : ℝ) ≤ d := d.cast_nonneg
  have hone : 1 ≤ x ^ (-a) * (d : ℝ) ^ a := by
    rw [Real.rpow_neg hx.le, ← div_eq_inv_mul, ← Real.div_rpow hd0 hx.le]
    exact Real.one_le_rpow ((one_le_div hx).2 hdx.le) ha
  calc s.nu d = s.nu d * 1 := (mul_one _).symm
    _ ≤ s.nu d * (x ^ (-a) * (d : ℝ) ^ a) := mul_le_mul_of_nonneg_left hone (hν d hd)
    _ = x ^ (-a) * (s.nu d * (d : ℝ) ^ a) := mul_left_comm _ _ _

/-- **The Legendre–Eratosthenes estimate with a divisor cutoff.** Let `0 < x`, `0 ≤ c` and
`0 ≤ σ ≤ 1`. If the approximate mass satisfies `0 ≤ X ≤ M x`, the remainders satisfy
`|R_d| ≤ c d ν(d)` for the divisors `d ≤ x` of the sifting product `P`, and the divisor sums `A_d`
vanish for the divisors `d > x`, then
`|S - X ∏_{p ∣ P} (1 - ν(p))| ≤ (c + M) x ^ σ ∏_{p ∣ P} (1 + ν(p) p ^ (1 - σ))`. -/
theorem abs_siftedSum_sub_totalMass_mul_prod_le_rpow_mul_prod (hx : 0 < x) (hc : 0 ≤ c)
    (hσ : 0 ≤ σ) (hσ' : σ ≤ 1) (hX : 0 ≤ s.totalMass) (hXM : s.totalMass ≤ M * x)
    (hrem : ∀ d ∈ s.prodPrimes.divisors, (d : ℝ) ≤ x → |s.rem d| ≤ c * ((d : ℝ) * s.nu d))
    (hmult : ∀ d ∈ s.prodPrimes.divisors, x < (d : ℝ) → s.multSum d = 0) :
    |s.siftedSum - s.totalMass * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
      (c + M) * x ^ σ * ∏ p ∈ s.prodPrimes.primeFactors, (1 + s.nu p * (p : ℝ) ^ (1 - σ)) := by
  set E : ℝ := ∏ p ∈ s.prodPrimes.primeFactors, (1 + s.nu p * (p : ℝ) ^ (1 - σ))
  set D : Finset ℕ := s.prodPrimes.divisors
  have hν (d : ℕ) (hd : d ∈ D) : 0 < s.nu d :=
    s.nu_pos_of_dvd_prodPrimes (dvd_of_mem_divisors hd)
  have hpow : x * x ^ (-(1 - σ)) = x ^ σ := by
    rw [mul_comm, ← Real.rpow_add_one hx.ne', neg_sub, sub_add_cancel]
  have hsmall : ∑ d ∈ D.filter fun d : ℕ ↦ (d : ℝ) ≤ x, |s.rem d| ≤ c * (x ^ σ * E) :=
    calc ∑ d ∈ D.filter fun d : ℕ ↦ (d : ℝ) ≤ x, |s.rem d|
        ≤ ∑ d ∈ D.filter fun d : ℕ ↦ (d : ℝ) ≤ x, c * ((d : ℝ) * s.nu d) :=
          sum_le_sum fun d hd ↦ hrem d (mem_filter.1 hd).1 (mem_filter.1 hd).2
      _ = c * ∑ d ∈ D.filter fun d : ℕ ↦ (d : ℝ) ≤ x, (d : ℝ) * s.nu d := (mul_sum ..).symm
      _ ≤ c * (x ^ σ * E) :=
          mul_le_mul_of_nonneg_left (s.sum_filter_le_mul_nu_le_rpow_mul_prod hx.le hσ) hc
  have hlarge : ∑ d ∈ D.filter fun d : ℕ ↦ ¬(d : ℝ) ≤ x, |s.rem d| ≤ M * (x ^ σ * E) :=
    calc ∑ d ∈ D.filter fun d : ℕ ↦ ¬(d : ℝ) ≤ x, |s.rem d|
        = s.totalMass * ∑ d ∈ D.filter fun d : ℕ ↦ x < (d : ℝ), s.nu d := by
          rw [mul_sum]
          refine sum_congr (filter_congr fun d _ ↦ not_le) fun d hd ↦ ?_
          obtain ⟨hd, hdx⟩ := mem_filter.1 hd
          rw [rem, hmult d hd hdx, zero_sub, abs_neg, abs_mul, abs_of_nonneg hX,
            abs_of_pos (hν d hd), mul_comm]
      _ ≤ M * x * (x ^ (-(1 - σ)) * E) :=
          mul_le_mul hXM (s.sum_filter_lt_nu_le_rpow_neg_mul_prod hx (sub_nonneg.2 hσ'))
            (sum_nonneg fun d hd ↦ (hν d (mem_filter.1 hd).1).le) (hX.trans hXM)
      _ = M * (x ^ σ * E) := by
          rw [← hpow]
          ring
  calc |s.siftedSum - s.totalMass * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)|
      ≤ ∑ d ∈ D, |s.rem d| := s.abs_siftedSum_sub_totalMass_mul_prod_le_sum_abs_rem
    _ = ∑ d ∈ D.filter fun d : ℕ ↦ (d : ℝ) ≤ x, |s.rem d| +
          ∑ d ∈ D.filter fun d : ℕ ↦ ¬(d : ℝ) ≤ x, |s.rem d| :=
        (sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ c * (x ^ σ * E) + M * (x ^ σ * E) := add_le_add hsmall hlarge
    _ = (c + M) * x ^ σ * E := by ring

/-! ### Examples -/

/-- At exponent `0` the density moment is the full density sum:
`∑_{d ∣ P} ν(d) = ∏_{p ∣ P} (1 + ν(p))`. -/
example : ∑ d ∈ s.prodPrimes.divisors, s.nu d = ∏ p ∈ s.prodPrimes.primeFactors, (1 + s.nu p) := by
  simpa using s.sum_nu_mul_rpow_eq_prod 0

/-- The cutoff bound at `σ = 0`: `∑_{d ∣ P, d ≤ x} d ν(d) ≤ ∏_{p ∣ P} (1 + ν(p) p)`. -/
example (hx : 0 ≤ x) :
    ∑ d ∈ s.prodPrimes.divisors.filter fun d : ℕ ↦ (d : ℝ) ≤ x, (d : ℝ) * s.nu d ≤
      ∏ p ∈ s.prodPrimes.primeFactors, (1 + s.nu p * (p : ℝ)) := by
  simpa using s.sum_filter_le_mul_nu_le_rpow_mul_prod hx le_rfl

/-- The tail bound at `a = 0`: the tail is at most the full density sum. -/
example (hx : 0 < x) :
    ∑ d ∈ s.prodPrimes.divisors.filter fun d : ℕ ↦ x < (d : ℝ), s.nu d ≤
      ∏ p ∈ s.prodPrimes.primeFactors, (1 + s.nu p) := by
  simpa using s.sum_filter_lt_nu_le_rpow_neg_mul_prod hx le_rfl

end BoundingSieve
