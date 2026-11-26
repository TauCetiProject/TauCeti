/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Bernoulli.Polynomials
import Mathlib.Algebra.Polynomial.Taylor
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.NumberTheory.Primorial

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

namespace Polynomial

/-- The coefficients of the Bernoulli polynomial translated by `x` are binomial multiples of
lower Bernoulli polynomials evaluated at `x`. -/
theorem coeff_taylor_bernoulli (x : ℚ) (n j : ℕ) :
    (taylor x (bernoulli n)).coeff j = (n.choose j : ℚ) * (bernoulli (n - j)).eval x := by
  have h (k : ℕ) : derivative^[k] (bernoulli n) = n.descFactorial k • bernoulli (n - k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, derivative_smul, derivative_bernoulli,
        Nat.descFactorial_succ, ← Nat.sub_sub]
      simp only [nsmul_eq_mul, Nat.cast_mul]
      ring
  have hz := congrFun (factorial_smul_hasseDeriv (R := ℚ) j) (bernoulli n)
  have hj : j.factorial • hasseDeriv j (bernoulli n) = _ := hz.trans (h j)
  have he := congrArg (eval x) hj
  simp only [nsmul_eq_mul, eval_mul, eval_natCast, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, mul_assoc] at he
  rw [taylor_coeff]
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (factorial_ne_zero j)) he

/-- The translation identity for Bernoulli polynomials, with coefficients in the Bernoulli basis. -/
theorem bernoulli_eval_add_eq_sum (n : ℕ) (x y : ℚ) :
    (bernoulli n).eval (x + y) = ∑ j ∈ range (n + 1),
      (n.choose j : ℚ) * (bernoulli (n - j)).eval x * y ^ j := by
  have hd : (taylor x (bernoulli n)).natDegree ≤ n :=
    natDegree_le_iff_coeff_eq_zero.mpr fun j hj ↦ by
      simp [coeff_taylor_bernoulli, Nat.choose_eq_zero_of_lt hj]
  rw [add_comm x, ← taylor_eval, eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  simp only [coeff_taylor_bernoulli]

end Polynomial

namespace TauCeti

/-- Faulhaber's identity for a shifted range of rational arguments. -/
theorem succ_mul_sum_range_add_pow_eq_bernoulli_sub (k m : ℕ) (x : ℚ) :
    ((k + 1 : ℕ) : ℚ) * (∑ j ∈ range m, (x + j) ^ k) =
      (Polynomial.bernoulli (k + 1)).eval (x + m) - (Polynomial.bernoulli (k + 1)).eval x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih]
    have hadd : x + (↑(m + 1) : ℚ) = 1 + (x + ↑m) := by push_cast; ring
    rw [hadd, Polynomial.bernoulli_eval_one_add]
    simp only [Nat.add_sub_cancel]
    ring

/-- A factorial of index greater than `l` clears the denominators of the homogenized Bernoulli
polynomial of degree `l` at every integer numerator and natural denominator. -/
theorem exists_intCast_eq_factorial_mul_pow_mul_bernoulli_eval {l k : ℕ} (hl : l < k)
    (N : ℕ) (a : ℤ) :
    ∃ b : ℤ, (b : ℚ) = (k.factorial : ℚ) * (N : ℚ) ^ l *
      (Polynomial.bernoulli l).eval ((a : ℚ) / N) := by
  rcases eq_or_ne N 0 with rfl | hN
  · cases l with
    | zero => exact ⟨k.factorial, by simp⟩
    | succ l => exact ⟨0, by simp⟩
  obtain ⟨d, hd⟩ := (primorial_dvd_primorial hl).trans (primorial_dvd_factorial k)
  obtain ⟨b, hb⟩ := exists_intCast_eq_primorial_mul_pow_mul_bernoulli_eval l hN a
  refine ⟨(d : ℤ) * b, ?_⟩
  push_cast
  rw [hb, hd, Nat.cast_mul]
  ring

/-- In a stretch of `m` consecutive terms of an arithmetic progression of step `N`, the sum of
`k`th powers multiplied by `(k + 1)!` differs from `m (k + 1)! N^k Bₖ(a/N)` by an integer multiple
of `m²`. The integer error allows the identity to be used in congruences without rational
coefficients. -/
theorem exists_factorial_mul_sum_range_add_mul_pow_sub_eq {N : ℕ} (hN : N ≠ 0)
    (k m : ℕ) (a : ℤ) :
    ∃ z : ℤ, ((k + 1).factorial : ℚ) * (∑ j ∈ range m, (a + (N : ℚ) * j) ^ k) -
      m * ((k + 1).factorial * (N : ℚ) ^ k * (Polynomial.bernoulli k).eval ((a : ℚ) / N)) =
      (m : ℚ) ^ 2 * z := by
  let x : ℚ := (a : ℚ) / N
  have hNQ : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hsum : ((k + 1).factorial : ℚ) * (∑ j ∈ range m, (a + (N : ℚ) * j) ^ k) =
      (k.factorial : ℚ) * (N : ℚ) ^ k *
        ((Polynomial.bernoulli (k + 1)).eval (x + m) -
          (Polynomial.bernoulli (k + 1)).eval x) := by
    have hterm (j : ℕ) : ((a : ℚ) + N * j) ^ k = (N : ℚ) ^ k * (x + j) ^ k := by
      rw [← mul_pow, mul_add]
      congr 2
      dsimp [x]
      field_simp
    simp_rw [hterm, ← mul_sum]
    rw [← succ_mul_sum_range_add_pow_eq_bernoulli_sub, Nat.factorial_succ, Nat.cast_mul]
    ring
  -- The constant Taylor term cancels; the linear term is the Bernoulli main term.
  rw [hsum, Polynomial.bernoulli_eval_add_eq_sum, sum_range_succ', sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, pow_zero, one_mul, mul_one,
    Nat.add_sub_cancel, Nat.add_sub_add_right]
  rw [Nat.choose_one_right, pow_one]
  let f (i : ℕ) : ℚ := ((k + 1).choose (i + 1 + 1) : ℚ) *
    (Polynomial.bernoulli (k - (i + 1))).eval x
  have htail (i : ℕ) (hi : i ∈ range k) : ∃ c : ℤ,
      (c : ℚ) = (k.factorial : ℚ) * (N : ℚ) ^ k * (f i * (m : ℚ) ^ i) := by
    let l := k - (i + 1)
    have hi' := mem_range.mp hi
    have hl : l + 1 ≤ k := by dsimp [l]; omega
    obtain ⟨b, hb⟩ := exists_intCast_eq_factorial_mul_pow_mul_bernoulli_eval hl N a
    refine ⟨(N : ℤ) ^ (k - l) * (k + 1).choose (i + 1 + 1) * b * (m : ℤ) ^ i, ?_⟩
    have hlk : l ≤ k := Nat.le_of_succ_le hl
    have hpow : (N : ℚ) ^ (k - l) * N ^ l = N ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hlk]
    push_cast
    rw [hb]
    dsimp [f]
    linear_combination ((k.factorial : ℚ) * (k + 1).choose (i + 1 + 1) *
      (Polynomial.bernoulli l).eval x * (m : ℚ) ^ i) * hpow
  choose c hc using htail
  refine ⟨∑ i ∈ (range k).attach, c i i.property, ?_⟩
  have hcast : (↑(∑ i ∈ (range k).attach, c i i.property) : ℚ) =
      (k.factorial : ℚ) * N ^ k * ∑ i ∈ range k, f i * (m : ℚ) ^ i := by
    push_cast
    simp only [hc, ← mul_sum]
    rw [sum_attach (range k) (fun i ↦ f i * (m : ℚ) ^ i)]
  rw [hcast, Nat.factorial_succ, Nat.cast_mul]
  have hscale : (∑ i ∈ range k, f i * (m : ℚ) ^ (i + 1 + 1)) =
      (m : ℚ) ^ 2 * ∑ i ∈ range k, f i * (m : ℚ) ^ i := by
    rw [mul_sum]
    exact sum_congr rfl fun i _ ↦ by rw [pow_succ, pow_succ]; ring
  rw [hscale]
  dsimp [x]
  ring

/-- For `N`-periodic weights, the factorial-scaled power sum at level `N * m` is congruent
modulo `m²` to `m` times the weighted sum of the integral Bernoulli values at level `N`. The
integer representatives `b` exist by `exists_intCast_eq_factorial_mul_pow_mul_bernoulli_eval`. -/
theorem sq_dvd_factorial_mul_sum_range_mul_pow_sub_bernoulli {R : Type*} [CommRing R]
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
  obtain ⟨z, hz⟩ := exists_factorial_mul_sum_range_add_mul_pow_sub_eq hN k m (a : ℤ)
  simp only [Int.cast_natCast] at hz
  rw [← hb a (mem_range.mp ha)] at hz
  have hzInt : ((k + 1).factorial : ℤ) *
        (∑ j ∈ range m, ((a : ℤ) + (N : ℤ) * (j : ℤ)) ^ k) - (m : ℤ) * b a =
        (m : ℤ) ^ 2 * z := by exact_mod_cast hz
  have hzR := congrArg (Int.castRingHom R) hzInt
  simp only [Int.coe_castRingHom] at hzR
  push_cast at hzR
  refine ⟨w a * (z : R), ?_⟩
  simp_rw [add_comm (a : R)] at hzR
  linear_combination w a * hzR

end TauCeti
