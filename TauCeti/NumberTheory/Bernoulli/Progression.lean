/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Bernoulli.Polynomials
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Bernoulli approximation of sums of powers in progressions

A power sum along `a, a + N, …, a + (m - 1)N`, after multiplication by `(k + 1)!`, is
congruent modulo `m²` to `m` times a scaled Bernoulli value at `a / N`. This is the
passage from sums of powers to Bernoulli values used in the twisted Voronoi congruence.
The normalization follows `New.OddPart.voronoi_congruence_bernoulli` in
`Lib/Cyclotomic/Voronoi.lean` of [lsernau/grh-lean](https://github.com/lsernau/grh-lean)
at `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Finset Nat

namespace TauCeti

/-- The factorial-scaled progression sum is a difference of homogenized Bernoulli values. -/
private theorem factorial_mul_sum_range_add_mul_pow_eq_bernoulli_sub {N : ℚ} (hN : N ≠ 0)
    (k m : ℕ) (a : ℚ) :
    ((k + 1).factorial : ℚ) * (∑ j ∈ range m, (a + N * j) ^ k) =
      (k.factorial : ℚ) * N ^ k * ((Polynomial.bernoulli (k + 1)).eval (a / N + m) -
        (Polynomial.bernoulli (k + 1)).eval (a / N)) := by
  have hterm (j : ℕ) : (a + N * j) ^ k = N ^ k * (a / N + j) ^ k := by
    rw [← mul_pow, mul_add, mul_comm N (a / N), div_mul_cancel₀ _ hN]
  simp_rw [hterm, ← mul_sum]
  rw [← succ_mul_sum_range_add_pow_eq_bernoulli_sub, Nat.factorial_succ, Nat.cast_mul]
  ring

/-- Separate the constant and linear terms in the translation formula for `Bₖ₊₁(x + y)`. -/
private theorem bernoulli_eval_add_eq_add_linear_add_sq_mul_sum (k : ℕ) (x y : ℚ) :
    (Polynomial.bernoulli (k + 1)).eval (x + y) = (Polynomial.bernoulli (k + 1)).eval x +
      ((k + 1 : ℕ) : ℚ) * (Polynomial.bernoulli k).eval x * y +
      y ^ 2 * ∑ i ∈ range k, ((k + 1).choose (i + 2) : ℚ) *
        (Polynomial.bernoulli (k - (i + 1))).eval x * y ^ i := by
  have hpow (i : ℕ) (c : ℚ) : c * y ^ (i + 2) = y ^ 2 * (c * y ^ i) := by
    rw [pow_add]
    ring
  rw [Polynomial.bernoulli_eval_add_eq_sum, sum_range_succ', sum_range_succ', mul_sum]
  simp [Nat.add_sub_add_right, hpow]
  ring

/-- Each term remaining after removal of the constant and linear terms is integral after
scaling by `k! N^k` and removing the common factor `m²`. -/
private theorem exists_intCast_eq_bernoulli_tail_term (k m N : ℕ) (a : ℤ) (i : ℕ) :
    ∃ c : ℤ, (c : ℚ) = (k.factorial : ℚ) * (N : ℚ) ^ k *
      (((k + 1).choose (i + 2) : ℚ) *
        (Polynomial.bernoulli (k - (i + 1))).eval ((a : ℚ) / N) * (m : ℚ) ^ i) := by
  rcases eq_or_ne k 0 with rfl | hk
  · have hi : 1 < i + 2 := by omega
    exact ⟨0, by simp [Nat.choose_eq_zero_of_lt hi]⟩
  let l := k - (i + 1)
  have hl : l < k := by dsimp [l]; omega
  obtain ⟨b, hb⟩ := exists_intCast_eq_factorial_mul_pow_mul_bernoulli_eval hl N a
  refine ⟨(N : ℤ) ^ (k - l) * (k + 1).choose (i + 2) * b * (m : ℤ) ^ i, ?_⟩
  have hpow : (N : ℚ) ^ (k - l) * N ^ l = N ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hl.le]
  push_cast
  rw [hb]
  linear_combination ((k.factorial : ℚ) * (k + 1).choose (i + 2) *
    (Polynomial.bernoulli l).eval ((a : ℚ) / N) * (m : ℚ) ^ i) * hpow

/-- In a stretch of `m` consecutive terms of an arithmetic progression of step `N`, the sum of
`k`th powers multiplied by `(k + 1)!` differs from `m (k + 1)! N^k Bₖ(a/N)` by an integer multiple
of `m²`. The integer error allows the identity to be used in congruences without rational
coefficients. -/
theorem exists_factorial_mul_sum_range_add_mul_pow_sub_mul_bernoulli_eval_eq_sq_mul
    {N : ℕ} (hN : N ≠ 0) (k m : ℕ) (a : ℤ) :
    ∃ z : ℤ, ((k + 1).factorial : ℚ) * (∑ j ∈ range m, (a + (N : ℚ) * j) ^ k) -
      m * ((k + 1).factorial * (N : ℚ) ^ k * (Polynomial.bernoulli k).eval ((a : ℚ) / N)) =
      (m : ℚ) ^ 2 * z := by
  -- Expand the endpoint difference; the constant term cancels and the linear term is the main term.
  rw [factorial_mul_sum_range_add_mul_pow_eq_bernoulli_sub (Nat.cast_ne_zero.mpr hN),
    bernoulli_eval_add_eq_add_linear_add_sq_mul_sum, Nat.factorial_succ, Nat.cast_mul]
  -- After removing `m²`, the error is a sum of integer casts.
  obtain ⟨z, hz⟩ : ∃ z : ℤ, (z : ℚ) = (k.factorial : ℚ) * (N : ℚ) ^ k *
      ∑ i ∈ range k, ((k + 1).choose (i + 2) : ℚ) *
        (Polynomial.bernoulli (k - (i + 1))).eval ((a : ℚ) / N) * (m : ℚ) ^ i := by
    rw [mul_sum]
    exact (Int.castRingHom ℚ).range.sum_mem fun i _ ↦
      exists_intCast_eq_bernoulli_tail_term k m N a i
  refine ⟨z, ?_⟩
  rw [hz]
  ring

/-- For `N`-periodic weights, the factorial-scaled power sum at level `N * m` is congruent
modulo `m²` to `m` times the weighted sum of the integral Bernoulli values at level `N`. The
integer representatives `b` exist by `exists_intCast_eq_factorial_mul_pow_mul_bernoulli_eval`. -/
theorem sq_dvd_factorial_mul_sum_range_mul_pow_sub_bernoulli {R : Type*} [Ring R]
    {N : ℕ} (k m : ℕ) {w : ℕ → R} (hw : Function.Periodic w N)
    {b : ℕ → ℤ} (hb : ∀ a < N, (b a : ℚ) = (k + 1).factorial * (N : ℚ) ^ k *
      (Polynomial.bernoulli k).eval ((a : ℚ) / N)) :
    (m : R) ^ 2 ∣ (k + 1).factorial * (∑ t ∈ range (N * m), w t * (t : R) ^ k) -
      (m : R) * ∑ a ∈ range N, w a * (b a : R) := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  rw [Finset.sum_range_mul_eq_sum_sum, Finset.sum_comm]
  have hw' (a j : ℕ) : w (N * j + a) = w a := by
    rw [add_comm, mul_comm N]
    exact hw.nat_mul j a
  simp_rw [hw', Nat.cast_add, Nat.cast_mul, ← mul_sum]
  rw [mul_sum, mul_sum, ← sum_sub_distrib]
  refine dvd_sum fun a ha ↦ ?_
  obtain ⟨z, hz⟩ :=
    exists_factorial_mul_sum_range_add_mul_pow_sub_mul_bernoulli_eval_eq_sq_mul hN k m (a : ℤ)
  simp only [Int.cast_natCast] at hz
  rw [← hb a (mem_range.mp ha)] at hz
  have hzInt : ((k + 1).factorial : ℤ) *
        (∑ j ∈ range m, ((N : ℤ) * (j : ℤ) + (a : ℤ)) ^ k) - (m : ℤ) * b a =
        (m : ℤ) ^ 2 * z := by
    simp_rw [add_comm _ (a : ℤ)]
    exact_mod_cast hz
  have hzR := congrArg (Int.castRingHom R) hzInt
  simp only [Int.coe_castRingHom] at hzR
  push_cast at hzR
  -- In a possibly noncommutative ring, only the scalar casts need to commute with the weight.
  have hfactor : ((k + 1).factorial : R) * (w a * ∑ j ∈ range m, ((N : R) * j + a) ^ k) -
      (m : R) * (w a * (b a : R)) =
      w a * (((k + 1).factorial : R) * (∑ j ∈ range m, ((N : R) * j + a) ^ k) -
        (m : R) * (b a : R)) := by
    rw [mul_sub, (Nat.cast_commute ((k + 1).factorial) (w a)).left_comm,
      (Nat.cast_commute m (w a)).left_comm]
  refine ⟨w a * (z : R), ?_⟩
  rw [hfactor, hzR, ((Nat.cast_commute m (w a)).pow_left 2).symm.left_comm]

end TauCeti
