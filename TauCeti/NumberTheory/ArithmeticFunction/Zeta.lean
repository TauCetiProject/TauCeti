/-
Copyright (c) 2026 The PrimeNumberTheoremAnd and Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PrimeNumberTheoremAnd contributors, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Linarith

/-!
# Convolution powers of the arithmetic zeta function

The Dirichlet-convolution powers of `ArithmeticFunction.zeta` are the fixed-order divisor
functions. Their prime-power coefficients are binomial coefficients, and these coefficients
are bounded by powers of the ordinary divisor count. The analytic subpower estimate is in
`TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds`.

The distinct-prime-factor powers are bounded by the corresponding divisor coefficients,
and the fourth divisor coefficient dominates the squared ordinary divisor count.

The prime-power argument is adapted from `d_apply_prime_pow` in
[Alex Kontorovich, Terence Tao and contributors, *Prime Number Theorem and More*][PNT].

The squared-divisor comparison is adapted from `ramanujan_tau_sq_le_zeta_pow_four` in
[Prime Number Theorem and More][PNT-square].

[PNT-square]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/3d28926f52e7cfcb2f872dcff7c6a5266579f7e5/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean#L622-L654

[PNT]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/88c889477b094e54ea4775cfbfd89c14a52791fe/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean#L361-L370
-/

public section

namespace ArithmeticFunction

open Finset Nat
open scoped zeta

/-- The prime-power coefficient of the `(k + 1)`-fold divisor function. -/
theorem zeta_pow_succ_apply_prime_pow (k a : ℕ) {p : ℕ} (hp : p.Prime) :
    (ζ ^ (k + 1)) (p ^ a) = (a + k).choose k := by
  induction k generalizing a with
  | zero => simp [hp.ne_zero]
  | succ k ih =>
    rw [pow_succ, mul_zeta_apply, sum_divisors_prime_pow hp]
    simp_rw [ih]
    simpa [add_assoc, add_left_comm, add_comm] using sum_range_add_choose a k

/-- Fixed-order divisor coefficients are bounded by powers of the ordinary divisor count. -/
theorem zeta_pow_succ_apply_le_card_divisors_pow (k n : ℕ) :
    (ζ ^ (k + 1)) n ≤ n.divisors.card ^ k := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hmult : (ζ ^ (k + 1) : ArithmeticFunction ℕ).IsMultiplicative :=
    isMultiplicative_zeta.pow
  rw [hmult.multiplicative_factorization _ hn, prod_factorization_eq_prod_primeFactors,
    Nat.card_divisors hn, ← Finset.prod_pow]
  apply Finset.prod_le_prod
  intro p hp
  rw [zeta_pow_succ_apply_prime_pow k _ (prime_of_mem_primeFactors hp)]
  exact Nat.choose_add_le_add_one_pow _ _

open scoped omega

/-- Distinct-prime-factor powers are bounded by fixed-order divisor coefficients. -/
theorem pow_cardDistinctFactors_le_zeta_pow (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    k ^ ω n ≤ (ζ ^ k : ArithmeticFunction ℕ) n := by
  cases k with
  | zero =>
    by_cases hn1 : n = 1
    · simp [hn1]
    · have hn_gt : 1 < n := by omega
      have hω : ω n ≠ 0 := (cardDistinctFactors_pos.mpr hn_gt).ne'
      simp [hn1, hω]
  | succ k =>
    rw [(isMultiplicative_zeta.pow (k := k + 1)).multiplicative_factorization _ hn,
      prod_factorization_eq_prod_primeFactors]
    calc
      (k + 1) ^ ω n = ∏ p ∈ n.primeFactors, (k + 1) := by
        rw [prod_const, cardDistinctFactors_eq_card_primeFactors]
      _ ≤ _ := by
        apply prod_le_prod
        intro p hp
        rw [zeta_pow_succ_apply_prime_pow k _ (prime_of_mem_primeFactors hp)]
        have ha : 1 ≤ n.factorization p :=
          (prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn (dvd_of_mem_primeFactors hp)
        calc
          k + 1 = (k + 1).choose k := (Nat.choose_succ_self_right k).symm
          _ ≤ _ := Nat.choose_le_choose k (by omega)

/-- The fourth fixed-order divisor coefficient dominates the squared divisor count. -/
theorem sigma_zero_sq_le_zeta_pow_four (n : ℕ) :
    (sigma 0 n) ^ 2 ≤ (ζ ^ 4 : ArithmeticFunction ℕ) n := by
  have hbound (a : ℕ) :
      (a + 1) ^ 2 ≤ (a + 3).choose 3 := by
    induction a with
    | zero => norm_num
    | succ a ih =>
      have h2 : 2 * a + 3 ≤ (a + 3).choose 2 := by
        rw [Nat.choose_two_right]
        have h : 2 * (2 * a + 3) ≤ (a + 3) * (a + 3 - 1) := by
          have ha : a + 3 - 1 = a + 2 := by omega
          rw [ha]
          nlinarith
        omega
      have hindex : a + 1 + 3 = (a + 3) + 1 := by omega
      rw [hindex, Nat.choose_succ_succ]
      nlinarith
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have ht : ((sigma 0).pmul (sigma 0)).IsMultiplicative :=
    (isMultiplicative_sigma (k := 0)).pmul (isMultiplicative_sigma (k := 0))
  have hsq : (sigma 0).pmul (sigma 0) n = (sigma 0 n) ^ 2 := by
    simp only [ArithmeticFunction.pmul_apply, pow_two]
  rw [← hsq, ht.multiplicative_factorization _ hn,
    (isMultiplicative_zeta.pow (k := 4)).multiplicative_factorization _ hn,
    prod_factorization_eq_prod_primeFactors, prod_factorization_eq_prod_primeFactors]
  apply Finset.prod_le_prod
  intro p hp
  have hpp := prime_of_mem_primeFactors hp
  simp only [ArithmeticFunction.pmul_apply]
  rw [← pow_two, sigma_zero_apply_prime_pow hpp, zeta_pow_succ_apply_prime_pow 3 _ hpp]
  exact hbound _

end ArithmeticFunction
