/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PrimeNumberTheoremAnd contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-!
# Fixed-order divisor bounds

The Dirichlet-convolution powers of `ArithmeticFunction.zeta` are the fixed-order divisor
functions. Their prime-power coefficients are binomial coefficients. Comparing those with
powers of the ordinary divisor count gives a subpolynomial bound for every fixed order.

The prime-power argument is adapted from `d_apply_prime_pow` in
[Alex Kontorovich, Terence Tao and contributors, *Prime Number Theorem and More*][PNT].

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

/-- Every fixed Dirichlet-convolution power of zeta is subpolynomial. The bound includes
order zero, which is the convolution identity, and index zero, where every coefficient is zero. -/
theorem exists_pos_zeta_pow_le_rpow (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ((ζ ^ k : ArithmeticFunction ℕ) n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  cases k with
  | zero =>
    refine ⟨1, by norm_num, fun n ↦ ?_⟩
    by_cases hn : n = 1
    · simp [hn]
    · simp only [pow_zero, ArithmeticFunction.one_apply_ne hn, Nat.cast_zero]
      positivity
  | succ k =>
    obtain ⟨C, hC, hbound⟩ := TauCeti.exists_pos_card_divisors_le_rpow
      (show 0 < ε / (k + 1 : ℝ) by positivity)
    refine ⟨C ^ (k + 1), by positivity, fun n ↦ ?_⟩
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Real.zero_rpow hε.ne']
    have hcard : 1 ≤ n.divisors.card :=
      Nat.one_le_iff_ne_zero.mpr (Finset.card_ne_zero.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩)
    calc
      ((ζ ^ (k + 1)) n : ℝ) ≤ (n.divisors.card : ℝ) ^ k := by
        exact_mod_cast zeta_pow_succ_apply_le_card_divisors_pow k n
      _ ≤ (n.divisors.card : ℝ) ^ (k + 1) :=
        pow_le_pow_right₀ (by exact_mod_cast hcard) (Nat.le_succ _)
      _ ≤ (C * (n : ℝ) ^ (ε / (k + 1 : ℝ))) ^ (k + 1) :=
        pow_le_pow_left₀ (by positivity) (hbound n) _
      _ = C ^ (k + 1) * (n : ℝ) ^ ε := by
        rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n),
          Nat.cast_add, Nat.cast_one, div_mul_cancel₀ _ (by positivity)]

end ArithmeticFunction
