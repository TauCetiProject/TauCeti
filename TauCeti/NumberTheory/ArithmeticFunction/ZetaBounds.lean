/-
Copyright (c) 2026 The PrimeNumberTheoremAnd and Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PrimeNumberTheoremAnd contributors, The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Mean bounds for ordered divisor functions

The Dirichlet-convolution powers of `ArithmeticFunction.zeta` count ordered factorizations.
Their harmonic and summatory means have coefficient-one bounds, with real cutoffs and
including convolution order zero. The pointwise comparisons give explicit mean bounds for
three to the number of distinct prime factors and for the squared ordinary divisor count.

The squared-divisor comparison is adapted from `ramanujan_tau_sq_le_zeta_pow_four` in
[Prime Number Theorem and More][PNT]. The earlier squarefree divisor majorants there are
Arend Mellendijk's 2023 formalization of Heath-Brown's Lemma 3.1; the bounds here sum over
all positive integers and improve the summatory logarithmic exponent.

[PNT]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/3d28926f52e7cfcb2f872dcff7c6a5266579f7e5/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean#L622-L654
-/

public section

open Finset Nat
open scoped ArithmeticFunction.zeta ArithmeticFunction.omega BigOperators

namespace ArithmeticFunction

private theorem sum_zeta_pow_succ_div_eq (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, ((ζ ^ (k + 1)) n : ℝ) / n) =
      ∑ d ∈ Ioc 0 N, ((ζ ^ k) d : ℝ) / d *
        ∑ m ∈ Ioc 0 (N / d), (m : ℝ)⁻¹ := by
  have h := sum_Ioc_mul_eq_sum_sum
    ((((ζ ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)).pdiv ↑ArithmeticFunction.id)
    (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ).pdiv ↑ArithmeticFunction.id) N
  have hdiv :
      ((((ζ ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) * ↑ζ).pdiv
        ↑ArithmeticFunction.id) =
      (((ζ ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℝ).pdiv ↑ArithmeticFunction.id) *
        (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ).pdiv ↑ArithmeticFunction.id) := by
    ext n
    simp only [pdiv_apply, natCoe_apply, id_apply, ArithmeticFunction.mul_apply, sum_div]
    apply sum_congr rfl
    intro a ha
    have hprod := (Nat.mem_divisorsAntidiagonal.mp ha).1
    rw [← hprod, Nat.cast_mul, mul_div_mul_comm]
  rw [← hdiv, ← natCoe_mul, ← pow_succ] at h
  have hinv (m : ℕ) :
      (((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ).pdiv ↑ArithmeticFunction.id) m =
        (m : ℝ)⁻¹ := by
    by_cases hm : m = 0 <;> simp [hm, pdiv_apply, natCoe_apply, id_apply, zeta_apply]
  simp_rw [hinv] at h
  simpa only [pdiv_apply, natCoe_apply, id_apply] using h

private theorem sum_Ioc_inv_eq_harmonic (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (n : ℝ)⁻¹ = (harmonic N : ℝ) := by
  simp [harmonic_eq_sum_Icc, ← Finset.Icc_add_one_left_eq_Ioc]

/-- The harmonic mean of the fixed-order divisor function is bounded by a power of the
ordinary harmonic sum, including cutoff zero and convolution order zero. -/
theorem sum_Ioc_zeta_pow_div_le_harmonic_pow (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, ((ζ ^ k) n : ℝ) / n) ≤ (harmonic N : ℝ) ^ k := by
  have hH : 0 ≤ (harmonic N : ℝ) := by
    rw [← sum_Ioc_inv_eq_harmonic]
    exact sum_nonneg fun n _ ↦ inv_nonneg.mpr (Nat.cast_nonneg n)
  induction k with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, ite_div, one_div, zero_div]
    rw [sum_ite_eq']
    split_ifs <;> norm_num
  | succ k ih =>
    rw [sum_zeta_pow_succ_div_eq, pow_succ]
    calc
      _ ≤ ∑ d ∈ Ioc 0 N, ((ζ ^ k) d : ℝ) / d * (harmonic N : ℝ) := by
        apply sum_le_sum
        intro d _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← sum_Ioc_inv_eq_harmonic]
        exact sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right (Nat.div_le_self N d))
          (by intros; positivity)
      _ = (∑ d ∈ Ioc 0 N, ((ζ ^ k) d : ℝ) / d) * (harmonic N : ℝ) := by
        rw [sum_mul]
      _ ≤ (harmonic N : ℝ) ^ k * (harmonic N : ℝ) :=
        mul_le_mul_of_nonneg_right ih hH

/-- The summatory fixed-order divisor function has the corresponding harmonic bound. -/
theorem sum_Ioc_zeta_pow_le_mul_harmonic_pow (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, ((ζ ^ k) n : ℝ)) ≤
      N * (harmonic N : ℝ) ^ (k - 1) := by
  cases k with
  | zero =>
    by_cases hN : N = 0
    · simp [hN]
    · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN
      simp [ArithmeticFunction.one_apply, sum_ite_eq', hN1]
  | succ k =>
    simp only [Nat.add_sub_cancel]
    have heq := sum_Ioc_mul_zeta_eq_sum (ζ ^ k) N (R := ℕ)
    simp only [natCoe_nat] at heq
    rw [pow_succ, ← Nat.cast_sum, heq, Nat.cast_sum]
    simp only [Nat.cast_mul]
    calc
      _ ≤ ∑ d ∈ Ioc 0 N, ((ζ ^ k) d : ℝ) * ((N : ℝ) / d) := by
        apply sum_le_sum
        intro d _
        exact mul_le_mul_of_nonneg_left Nat.cast_div_le (by positivity)
      _ = N * ∑ d ∈ Ioc 0 N, ((ζ ^ k) d : ℝ) / d := by
        rw [mul_sum]
        apply sum_congr rfl
        intro d _
        ring
      _ ≤ N * (harmonic N : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left (sum_Ioc_zeta_pow_div_le_harmonic_pow k N) (by positivity)

/-- The harmonic ordered-divisor bound with a real cutoff and coefficient one. -/
theorem sum_Ioc_zeta_pow_div_le_one_add_log_pow (k : ℕ) {Z : ℝ} (hZ : 1 ≤ Z) :
    (∑ n ∈ Ioc 0 ⌊Z⌋₊, ((ζ ^ k) n : ℝ) / n) ≤ (1 + Real.log Z) ^ k := by
  have hH : 0 ≤ (harmonic ⌊Z⌋₊ : ℝ) := by
    rw [← sum_Ioc_inv_eq_harmonic]
    exact sum_nonneg fun n _ ↦ inv_nonneg.mpr (Nat.cast_nonneg n)
  exact (sum_Ioc_zeta_pow_div_le_harmonic_pow k ⌊Z⌋₊).trans
    (pow_le_pow_left₀ hH (harmonic_floor_le_one_add_log Z hZ) k)

/-- The summatory ordered-divisor bound with a real cutoff and coefficient one. -/
theorem sum_Ioc_zeta_pow_le_mul_one_add_log_pow (k : ℕ) {Z : ℝ} (hZ : 1 ≤ Z) :
    (∑ n ∈ Ioc 0 ⌊Z⌋₊, ((ζ ^ k) n : ℝ)) ≤
      Z * (1 + Real.log Z) ^ (k - 1) := by
  have hH : 0 ≤ (harmonic ⌊Z⌋₊ : ℝ) := by
    rw [← sum_Ioc_inv_eq_harmonic]
    exact sum_nonneg fun n _ ↦ inv_nonneg.mpr (Nat.cast_nonneg n)
  exact (sum_Ioc_zeta_pow_le_mul_harmonic_pow k ⌊Z⌋₊).trans
    (mul_le_mul (Nat.floor_le (zero_le_one.trans hZ))
      (pow_le_pow_left₀ hH (harmonic_floor_le_one_add_log Z hZ) (k - 1))
      (pow_nonneg hH _) (zero_le_one.trans hZ))

/-- Distinct-prime-factor powers are bounded by fixed-order divisor coefficients. -/
theorem pow_cardDistinctFactors_le_zeta_pow (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    k ^ ω n ≤ (ζ ^ k : ArithmeticFunction ℕ) n := by
  cases k with
  | zero =>
    by_cases hn1 : n = 1
    · simp [hn1]
    · have hω : ω n ≠ 0 := by simpa using (show ¬ n ≤ 1 by omega)
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
      rw [show a + 1 + 3 = (a + 3) + 1 by omega, Nat.choose_succ_succ]
      nlinarith
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have ht : ((sigma 0).pmul (sigma 0)).IsMultiplicative :=
    (isMultiplicative_sigma (k := 0)).pmul (isMultiplicative_sigma (k := 0))
  rw [← show (sigma 0).pmul (sigma 0) n = (sigma 0 n) ^ 2 from (pow_two _).symm,
    ht.multiplicative_factorization _ hn,
    (isMultiplicative_zeta.pow (k := 4)).multiplicative_factorization _ hn,
    prod_factorization_eq_prod_primeFactors, prod_factorization_eq_prod_primeFactors]
  apply Finset.prod_le_prod
  intro p hp
  have hpp := prime_of_mem_primeFactors hp
  simp only [ArithmeticFunction.pmul_apply]
  rw [← pow_two, sigma_zero_apply_prime_pow hpp, zeta_pow_succ_apply_prime_pow 3 _ hpp]
  exact hbound _

/-- A coefficient-one summatory bound for three to the number of distinct prime factors. -/
theorem sum_Ioc_three_pow_cardDistinctFactors_le_mul_one_add_log_sq {Z : ℝ} (hZ : 1 ≤ Z) :
    (∑ n ∈ Ioc 0 ⌊Z⌋₊, (3 : ℝ) ^ ω n) ≤ Z * (1 + Real.log Z) ^ 2 := by
  refine le_trans (sum_le_sum fun n hn ↦ ?_) (sum_Ioc_zeta_pow_le_mul_one_add_log_pow 3 hZ)
  exact_mod_cast pow_cardDistinctFactors_le_zeta_pow 3 (ne_of_gt (mem_Ioc.mp hn).1)

/-- A coefficient-one summatory bound for the squared ordinary divisor function. -/
theorem sum_Ioc_sigma_zero_sq_le_mul_one_add_log_cube {Z : ℝ} (hZ : 1 ≤ Z) :
    (∑ n ∈ Ioc 0 ⌊Z⌋₊, (sigma 0 n : ℝ) ^ 2) ≤ Z * (1 + Real.log Z) ^ 3 := by
  refine le_trans (sum_le_sum fun n _ ↦ ?_) (sum_Ioc_zeta_pow_le_mul_one_add_log_pow 4 hZ)
  exact_mod_cast sigma_zero_sq_le_zeta_pow_four n

end ArithmeticFunction
