/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SelbergSieve
import TauCeti.NumberTheory.ArithmeticFunction.Moebius

/-!
# The Legendre identity and lower sieve coefficients

For a Mathlib bounding sieve with sifting product `P`, approximate mass `X`, density `ν`,
divisor sums `A_d` and remainders `R_d = A_d - ν(d) X`, this file proves the finite
inclusion-exclusion identities and inequalities underlying combinatorial sieves.

* `BoundingSieve.sum_mul_multSum_eq_sum_support_mul_sum_divisors_gcd`: for an arbitrary signed
  coefficient function `c`, `∑_{d ∣ P} c(d) A_d = ∑_{n} w(n) ∑_{d ∣ gcd(P, n)} c(d)`.
* `BoundingSieve.siftedSum_eq_sum_moebius_mul_multSum`: Legendre's identity
  `S = ∑_{d ∣ P} μ(d) A_d`.
* `BoundingSieve.siftedSum_eq_totalMass_mul_prod_add_sum_moebius_mul_rem`: the Euler-product
  main term with signed remainder, `S = X ∏_{p ∣ P} (1 - ν(p)) + ∑_{d ∣ P} μ(d) R_d`.
* `BoundingSieve.abs_siftedSum_sub_totalMass_mul_prod_le_sum_abs_rem`: the Legendre error bound
  `|S - X ∏_{p ∣ P} (1 - ν(p))| ≤ ∑_{d ∣ P} |R_d|`.
* `BoundingSieve.sum_mul_multSum_le_siftedSum` and
  `BoundingSieve.totalMass_mul_mainSum_sub_errSum_le_siftedSum`: lower sieve coefficients,
  those with `∑_{d ∣ r} c(d) ≤ 1_{r = 1}` for every `r ∣ P`, bound the sifted sum below.
  These are the lower counterparts of Mathlib's
  `BoundingSieve.siftedSum_le_sum_of_upperMoebius` and
  `BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius`.
* `BoundingSieve.errSum_le_mul_sum_abs_rem`: the error of coefficients supported on `d ≤ D`
  and bounded by `C` there is at most `C ∑_{d ∣ P, d ≤ D} |R_d|`.
* `BoundingSieve.multSum_one_sub_sum_multSum_le_siftedSum`: the first Bonferroni lower bound
  `A_1 - ∑_{p ∣ P} A_p ≤ S`.

No normalization `X = A_1` and no sign condition on `X` is assumed, so the remainder `R_1` is
retained throughout.

## References

* D. R. Heath-Brown, *Lectures on sieves*, arXiv:math/0209360, §1, (1.1)-(1.8).
* K. S. Kedlaya, *Notes on analytic number theory*, Chapter 11, Lemma 11.1.

The divisor-sum interchange follows the proof of Mathlib's
`BoundingSieve.siftedSum_le_sum_of_upperMoebius`, by Arend Mellendijk.
-/

public section

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace BoundingSieve

/-- The weighted divisibility interchange: a signed combination of the divisor sums `A_d` over
the divisors of the sifting product is the weighted sum, over the support, of the coefficients
summed over the divisors of `gcd(P, n)`. -/
theorem sum_mul_multSum_eq_sum_support_mul_sum_divisors_gcd (s : BoundingSieve) (c : ℕ → ℝ) :
    ∑ d ∈ s.prodPrimes.divisors, c d * s.multSum d =
      ∑ n ∈ s.support, s.weights n * ∑ d ∈ (s.prodPrimes.gcd n).divisors, c d := by
  calc
    _ = ∑ n ∈ s.support, ∑ d ∈ s.prodPrimes.divisors,
        if d ∣ n then s.weights n * c d else 0 := by
      rw [sum_comm]
      simp_rw [multSum, ← sum_filter, mul_sum, mul_comm]
    _ = _ := by
      simp_rw [mul_sum, ← sum_filter]
      refine sum_congr rfl fun n _ ↦ ?_
      rw [← divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero (Nat.gcd_dvd_left _ _)]
      refine sum_congr ?_ fun _ _ ↦ rfl
      ext d
      simp +contextual [dvd_gcd_iff]

/-- Legendre's identity: the sifted sum is the Möbius combination of the divisor sums `A_d`
over the divisors of the sifting product. -/
theorem siftedSum_eq_sum_moebius_mul_multSum (s : BoundingSieve) :
    s.siftedSum = ∑ d ∈ s.prodPrimes.divisors, (μ d : ℝ) * s.multSum d := by
  rw [sum_mul_multSum_eq_sum_support_mul_sum_divisors_gcd, siftedSum_eq_sum_support_mul_ite]
  refine sum_congr rfl fun n _ ↦ ?_
  have h := coe_mul_zeta_apply (f := (μ : ArithmeticFunction ℝ)) (x := s.prodPrimes.gcd n)
  simp only [coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply, intCoe_apply] at h
  rw [h]

/-- Legendre's identity with the Euler-product main term and the signed remainder:
`S = X ∏_{p ∣ P} (1 - ν(p)) + ∑_{d ∣ P} μ(d) R_d`. -/
theorem siftedSum_eq_totalMass_mul_prod_add_sum_moebius_mul_rem (s : BoundingSieve) :
    s.siftedSum = s.totalMass * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p) +
      ∑ d ∈ s.prodPrimes.divisors, (μ d : ℝ) * s.rem d := by
  rw [siftedSum_eq_sum_moebius_mul_multSum,
    s.nu_mult.prodPrimeFactors_one_sub _ s.prodPrimes_ne_zero, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun d _ ↦ ?_
  rw [multSum_eq_main_err]
  ring

/-- The Legendre error bound: the sifted sum differs from its Euler-product main term by at most
the sum of all absolute remainders, including `|R_1|`. -/
theorem abs_siftedSum_sub_totalMass_mul_prod_le_sum_abs_rem (s : BoundingSieve) :
    |s.siftedSum - s.totalMass * ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)| ≤
      ∑ d ∈ s.prodPrimes.divisors, |s.rem d| := by
  rw [siftedSum_eq_totalMass_mul_prod_add_sum_moebius_mul_rem, add_sub_cancel_left]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ ↦ ?_)
  exact abs_moebius_mul_le d _

/-- Lower sieve coefficients bound the sifted sum below: if `∑_{d ∣ r} c(d) ≤ 1_{r = 1}` for
every divisor `r` of the sifting product, then `∑_{d ∣ P} c(d) A_d ≤ S`. -/
theorem sum_mul_multSum_le_siftedSum (s : BoundingSieve) {c : ℕ → ℝ}
    (hc : ∀ r, r ∣ s.prodPrimes → ∑ d ∈ r.divisors, c d ≤ if r = 1 then 1 else 0) :
    ∑ d ∈ s.prodPrimes.divisors, c d * s.multSum d ≤ s.siftedSum := by
  rw [sum_mul_multSum_eq_sum_support_mul_sum_divisors_gcd, siftedSum_eq_sum_support_mul_ite]
  gcongr with n
  exact hc _ (Nat.gcd_dvd_left _ _)

/-- Lower sieve coefficients bound the sifted sum below by the main term minus the absolute
error: `X · mainSum c - errSum c ≤ S`. No sign condition on `X` is needed. -/
theorem totalMass_mul_mainSum_sub_errSum_le_siftedSum (s : BoundingSieve) {c : ℕ → ℝ}
    (hc : ∀ r, r ∣ s.prodPrimes → ∑ d ∈ r.divisors, c d ≤ if r = 1 then 1 else 0) :
    s.totalMass * s.mainSum c - s.errSum c ≤ s.siftedSum := by
  refine le_trans ?_ (s.sum_mul_multSum_le_siftedSum hc)
  rw [mainSum, errSum, mul_sum, ← sum_sub_distrib]
  refine sum_le_sum fun d _ ↦ ?_
  rw [multSum_eq_main_err, ← abs_mul]
  linarith [neg_abs_le (c d * s.rem d)]

/-- The error of coefficients supported on the divisors `d ≤ D` and bounded by `C` in absolute
value there is at most `C ∑_{d ∣ P, d ≤ D} |R_d|`. -/
theorem errSum_le_mul_sum_abs_rem (s : BoundingSieve) {c : ℕ → ℝ} {D : ℕ} {C : ℝ}
    (hsupp : ∀ d, d ∣ s.prodPrimes → D < d → c d = 0)
    (hC : ∀ d, d ∣ s.prodPrimes → d ≤ D → |c d| ≤ C) :
    s.errSum c ≤ C * ∑ d ∈ s.prodPrimes.divisors with d ≤ D, |s.rem d| := by
  rw [errSum, ← sum_filter_add_sum_filter_not _ (· ≤ D), mul_sum]
  rw [sum_eq_zero (s := {d ∈ s.prodPrimes.divisors | ¬d ≤ D}) fun d hd ↦ by
    simp only [mem_filter, mem_divisors, not_le] at hd
    simp [hsupp d hd.1.1 hd.2], add_zero]
  refine sum_le_sum fun d hd ↦ ?_
  simp only [mem_filter, mem_divisors] at hd
  exact mul_le_mul_of_nonneg_right (hC d hd.1.1 hd.2) (abs_nonneg _)

/-- The first Bonferroni lower bound: `A_1 - ∑_{p ∣ P} A_p ≤ S`. The left side may be
negative. -/
theorem multSum_one_sub_sum_multSum_le_siftedSum (s : BoundingSieve) :
    s.multSum 1 - ∑ p ∈ s.prodPrimes.primeFactors, s.multSum p ≤ s.siftedSum := by
  let c : ℕ → ℝ := fun d ↦ (if d = 1 then 1 else 0) - if d.Prime then 1 else 0
  have hsum (r : ℕ) (hr : r ≠ 0) :
      ∑ d ∈ r.divisors, c d = 1 - (r.primeFactors.card : ℝ) := by
    simp [c, sum_sub_distrib, primeFactors_eq_to_filter_divisors_prime, hr]
  convert s.sum_mul_multSum_le_siftedSum (c := c) fun r hr ↦ ?_ using 1
  · simp [c, sub_mul, ite_mul, sum_sub_distrib, ← sum_filter,
      primeFactors_eq_to_filter_divisors_prime, s.prodPrimes_ne_zero]
  · have hr0 : r ≠ 0 := ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero hr
    rw [hsum r hr0]
    split_ifs with h1
    · simp [h1]
    · have : r.primeFactors.Nonempty := nonempty_primeFactors.mpr (by omega)
      have := this.card_pos
      simp only [sub_nonpos, one_le_cast]
      omega

end BoundingSieve
