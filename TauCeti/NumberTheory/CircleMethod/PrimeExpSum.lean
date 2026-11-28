/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import TauCeti.NumberTheory.CircleMethod.AdditiveCharacter

/-!
# The von Mangoldt exponential sum

The sum `primeExpSum N α = ∑_{n=1}^N Λ(n) e(nα)` includes all prime powers, with the
von Mangoldt weight. It is continuous and periodic with period one, and its value at zero
is Chebyshev's `psi` function.

`integral_norm_sq_primeExpSum` is Parseval's identity on the unit interval. Together with
`sum_sq_vonMangoldt_le`, it bounds the mean square by `(log 4 + 4) N log N`.
This energy bound converts a pointwise saving on the minor arcs into a bound for the
integral of the cube, as needed in the circle method for sums of three primes.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Springer, 2000, Chapter 25.
-/

public section

noncomputable section

open Finset ArithmeticFunction

namespace TauCeti

/-- The exponential sum `∑_{n=1}^N Λ(n) exp(2πinα)`, with von Mangoldt weights.
Prime powers as well as primes contribute. -/
def primeExpSum (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, (vonMangoldt n : ℂ) * expTwoPiI (n * α)

theorem primeExpSum_def (N : ℕ) (α : ℝ) :
    primeExpSum N α = ∑ n ∈ Icc 1 N, (vonMangoldt n : ℂ) * expTwoPiI (n * α) := (rfl)

@[simp]
theorem primeExpSum_zero (α : ℝ) : primeExpSum 0 α = 0 := by
  simp [primeExpSum_def]

@[simp]
theorem primeExpSum_one (α : ℝ) : primeExpSum 1 α = 0 := by
  simp [primeExpSum_def]

/-- Increasing the cutoff by one adds the corresponding von Mangoldt term. -/
theorem primeExpSum_succ (N : ℕ) (α : ℝ) :
    primeExpSum (N + 1) α = primeExpSum N α +
      (vonMangoldt (N + 1) : ℂ) * expTwoPiI ((N + 1) * α) := by
  simp only [primeExpSum_def, sum_Icc_succ_top (by omega : 1 ≤ N + 1), Nat.cast_add,
    Nat.cast_one]

/-- At zero the exponential sum is Chebyshev's `psi`, including the prime powers. -/
@[simp]
theorem primeExpSum_zero_right (N : ℕ) : primeExpSum N 0 = Chebyshev.psi N := by
  simp [primeExpSum_def, Chebyshev.psi, ← Icc_add_one_left_eq_Ioc]

/-- Negating the phase conjugates the exponential sum. -/
theorem primeExpSum_neg (N : ℕ) (α : ℝ) :
    primeExpSum N (-α) = starRingEnd ℂ (primeExpSum N α) := by
  simp [primeExpSum_def, map_sum, mul_neg]

@[simp]
theorem conj_primeExpSum (N : ℕ) (α : ℝ) :
    starRingEnd ℂ (primeExpSum N α) = primeExpSum N (-α) :=
  (primeExpSum_neg N α).symm

/-- The von Mangoldt exponential sum has period one. -/
theorem primeExpSum_periodic (N : ℕ) : Function.Periodic (primeExpSum N) 1 := by
  intro α
  simp only [primeExpSum_def, mul_add, mul_one, expTwoPiI_natCast_mul]
  simp [expTwoPiI_add, expTwoPiI_natCast_mul]

/-- The von Mangoldt exponential sum is continuous in its phase. -/
@[fun_prop]
theorem continuous_primeExpSum (N : ℕ) : Continuous (primeExpSum N) := by
  unfold primeExpSum
  apply continuous_finsetSum
  intro n _
  simp only [expTwoPiI_def]
  fun_prop

/-- The trivial pointwise bound by Chebyshev's `psi` function. -/
theorem norm_primeExpSum_le_psi (N : ℕ) (α : ℝ) :
    ‖primeExpSum N α‖ ≤ Chebyshev.psi N := by
  rw [primeExpSum_def, Chebyshev.psi]
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖(vonMangoldt n : ℂ) * expTwoPiI (n * α)‖ := norm_sum_le _ _
    _ = _ := by simp [← Icc_add_one_left_eq_Ioc, abs_of_nonneg vonMangoldt_nonneg]

/-- The second moment of the von Mangoldt coefficients is at most `log N * psi N`. -/
theorem sum_sq_vonMangoldt_le_log_mul_psi (N : ℕ) :
    ∑ n ∈ Icc 1 N, vonMangoldt n ^ 2 ≤ Real.log N * Chebyshev.psi N := by
  rw [Chebyshev.psi]
  simp only [Nat.floor_natCast, ← Icc_add_one_left_eq_Ioc, zero_add, mul_sum]
  apply sum_le_sum
  intro n hn
  have hlog : vonMangoldt n ≤ Real.log N := vonMangoldt_le_log.trans
    (Real.log_le_log (by exact_mod_cast (mem_Icc.mp hn).1)
      (by exact_mod_cast (mem_Icc.mp hn).2))
  nlinarith [vonMangoldt_nonneg (n := n)]

/-- Chebyshev's bound gives the uniform coefficient energy estimate, also at `N = 0`. -/
theorem sum_sq_vonMangoldt_le (N : ℕ) :
    ∑ n ∈ Icc 1 N, vonMangoldt n ^ 2 ≤
      (Real.log 4 + 4) * N * Real.log N := by
  calc
    _ ≤ Real.log N * Chebyshev.psi N := sum_sq_vonMangoldt_le_log_mul_psi N
    _ ≤ Real.log N * ((Real.log 4 + 4) * N) :=
      mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self (by positivity))
        (Real.log_natCast_nonneg N)
    _ = _ := by ring

/-- **Parseval's identity** for the von Mangoldt exponential sum on the unit interval. -/
theorem integral_norm_sq_primeExpSum (N : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖primeExpSum N α‖ ^ 2 =
      ∑ n ∈ Icc 1 N, vonMangoldt n ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  -- Expanding against the conjugate gives integer difference frequencies.
  have hexpand (α : ℝ) : (‖primeExpSum N α‖ ^ 2 : ℂ) =
      ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
        ((vonMangoldt n * vonMangoldt m : ℝ) : ℂ) *
          expTwoPiI (((m : ℤ) - n : ℤ) * α) := by
    rw [← Complex.mul_conj', primeExpSum_def]
    simp only [map_sum, map_mul, Complex.conj_ofReal, conj_expTwoPiI, sum_mul, mul_sum]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro m _
    push_cast
    rw [sub_mul, sub_eq_add_neg, expTwoPiI_add]
    ring
  simp only [Complex.ofReal_pow]
  simp_rw [hexpand]
  have hint (n m : ℕ) : IntervalIntegrable
      (fun α : ℝ ↦ ((vonMangoldt n * vonMangoldt m : ℝ) : ℂ) *
        expTwoPiI (((m : ℤ) - n : ℤ) * α)) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    simp only [expTwoPiI_def]
    fun_prop
  -- Continuity permits termwise integration; orthogonality removes the off-diagonal terms.
  rw [intervalIntegral.integral_finsetSum (fun n _ ↦ by
    convert IntervalIntegrable.sum (Icc 1 N) (fun m _ ↦ hint n m) using 1
    ext α
    simp only [Finset.sum_apply])]
  simp_rw [intervalIntegral.integral_finsetSum (fun m _ ↦ hint _ m),
    intervalIntegral.integral_const_mul, integral_expTwoPiI_intCast]
  push_cast
  apply sum_congr rfl
  intro n hn
  simp [sub_eq_zero, mul_ite, mem_Icc.mp hn, sq]

/-- The mean square of the exponential sum is at most `(log 4 + 4) N log N`. -/
theorem integral_norm_sq_primeExpSum_le (N : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖primeExpSum N α‖ ^ 2 ≤
      (Real.log 4 + 4) * N * Real.log N := by
  rw [integral_norm_sq_primeExpSum]
  exact sum_sq_vonMangoldt_le N

/-! ### Small cutoffs -/

example (α : ℝ) : primeExpSum 2 α = (Real.log 2 : ℂ) * expTwoPiI (2 * α) := by
  convert primeExpSum_succ 1 α using 1
  norm_num [vonMangoldt_apply_prime Nat.prime_two]

/-- The term at `4` is present, with the same von Mangoldt weight as the term at `2`. -/
example : primeExpSum 4 0 = (Real.log 12 : ℂ) := by
  have h4 : vonMangoldt 4 = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by rfl, vonMangoldt_apply_pow (by decide)]
    exact vonMangoldt_apply_prime Nat.prime_two
  rw [primeExpSum_succ 3, primeExpSum_succ 2, primeExpSum_succ 1]
  simp only [Nat.reduceAdd, h4, vonMangoldt_apply_prime Nat.prime_two,
    vonMangoldt_apply_prime Nat.prime_three, primeExpSum_one, mul_zero, expTwoPiI_zero,
    mul_one, zero_add]
  rw [show (12 : ℝ) = 2 * 3 * 2 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  push_cast
  ring

end TauCeti
