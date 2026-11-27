/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Bernoulli polynomials and Bernoulli functions

Mathlib's `bernoulliFun` is the real-variable Bernoulli polynomial. This file records how it
relates to the Bernoulli polynomial over `ℚ`, and how the even ones compare with their value at
`0` on `[0, 1]`.

## Main results

* `TauCeti.bernoulliFun_ratCast`: `bernoulliFun` at a rational point is the Bernoulli polynomial
  over `ℚ` evaluated there, mapped into `ℝ`.
* `TauCeti.neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg`: on `[0, 1]`,
  `B_{2k} - B_{2k}(x)` has the sign `(-1)^(k+1)` of `B_{2k}` (or vanishes). This makes the
  remainder of the Euler–Maclaurin formula of even order a one-signed integral, so that for
  monotone derivatives the remainder is enclosed by the first neglected term.
* `TauCeti.abs_bernoulliFun_le_mul_tsum`: for `2 ≤ k` and `x ∈ [0, 1]`,
  `|B_k(x)| ≤ 2 · k! / (2π)^k · ∑_{n : ℕ} 1 / n^k`, the last sum being `ζ(k)`.
* `TauCeti.abs_bernoulliFun_le_pi_sq_div_three_mul_factorial_div`: for every `k` and
  `x ∈ [0, 1]`, `|B_k(x)| ≤ π² / 3 · k! / (2π)^k`; equality holds for `k = 2`, `x = 0`.
* `TauCeti.abs_bernoulliFun_le_four_mul_factorial_div`: the weaker
  `|B_k(x)| ≤ 4 · k! / (2π)^k`.
* `TauCeti.abs_eval_bernoulli_le_four_mul_factorial_div`: the same bound for the Bernoulli
  polynomial over `ℚ` at a rational point of `[0, 1]`.
* `TauCeti.abs_eval_bernoulli_natCast_div_le_four_mul_factorial_div`: its specialisation to the
  points `n / N` with `n ≤ N`.

The sign follows from the Fourier series `hasSum_one_div_nat_pow_mul_cos`: up to the positive
factor `(2π)^(2k) / (2 (2k)!)`, `(-1)^(k+1) (B_{2k} - B_{2k}(x))` is
`∑_{n ≥ 1} (1 - cos (2π n x)) / n^(2k) ≥ 0`.

The uniform bounds follow from the Fourier series `hasSum_one_div_nat_pow_mul_fourier`:
`-(2πi)^k / k! · B_k(x) = ∑_{n ≥ 1} n^(-k) (e(nx) + (-1)^k e(-nx))` for `k ≥ 2`, whose terms
have norm at most `2 n^(-k)`, together with `ζ(k) ≤ ζ(2) = π² / 6`; the cases `k = 0, 1` are
checked directly.

## References

* The bound `|B_k(x)| ≤ 4 · k! / (2π)^k` on `[0, 1]` is the estimate used to bound generalized
  Bernoulli numbers in the proof of `UpperTheory.V.Odd.PrimeBound` in
  https://github.com/leanprover-community/riemann-hypothesis, the source of the statement.
* The Fourier series of Bernoulli polynomials: DLMF 24.8.1–24.8.2.
-/

public section

namespace TauCeti

/-- `bernoulliFun` at a rational point is the Bernoulli polynomial over `ℚ` evaluated there,
mapped into `ℝ`. -/
theorem bernoulliFun_ratCast (k : ℕ) (x : ℚ) :
    bernoulliFun k (x : ℝ) = (((Polynomial.bernoulli k).eval x : ℚ) : ℝ) := by
  simp only [bernoulliFun, Polynomial.eval_map, ← map_ratCast (algebraMap ℚ ℝ),
    Polynomial.eval₂_at_apply]
  norm_cast

/-- On `[0, 1]` the even Bernoulli polynomial lies on one side of its value at `0`:
`(-1)^(k+1) (B_{2k} - B_{2k}(x)) ≥ 0`, so `B_{2k} - B_{2k}(x)` has the sign of `B_{2k}`. -/
theorem neg_one_pow_mul_bernoulli_sub_bernoulliFun_nonneg (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ (-1) ^ (k + 1) * (bernoulli (2 * k) - bernoulliFun (2 * k) x) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hx' := hasSum_one_div_nat_pow_mul_cos hk hx
  have h0 := hasSum_one_div_nat_pow_mul_cos hk (Set.left_mem_Icc.mpr zero_le_one)
  rw [← bernoulliFun] at hx' h0
  rw [bernoulliFun_eval_zero] at h0
  -- Termwise, `cos (2π n x) / n^(2k) ≤ 1 / n^(2k)`.
  have hle := hasSum_le (fun n => ?_) hx' h0
  · have hC : (0 : ℝ) < (2 * Real.pi) ^ (2 * k) / 2 / (2 * k).factorial := by positivity
    have : 0 ≤ (2 * Real.pi) ^ (2 * k) / 2 / (2 * k).factorial *
        ((-1) ^ (k + 1) * (bernoulli (2 * k) - bernoulliFun (2 * k) x)) := by
      convert sub_nonneg.mpr hle using 1
      ring
    exact nonneg_of_mul_nonneg_right this hC
  · simp only [mul_zero, Real.cos_zero, mul_one]
    exact mul_le_of_le_one_right (by positivity) (Real.cos_le_one _)

open scoped Nat Real

/-- For `2 ≤ k` and `x ∈ [0, 1]`, `|B_k(x)| ≤ 2 · k! / (2π)^k · ∑_{n : ℕ} 1 / n^k`, i.e.
`|B_k(x)| ≤ 2 · k! · ζ(k) / (2π)^k`. Everything is in `ℝ`, and the `n = 0` term of the sum is
`1 / 0 = 0`. -/
theorem abs_bernoulliFun_le_mul_tsum {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |bernoulliFun k x| ≤ 2 * k ! / (2 * π) ^ k * ∑' n : ℕ, 1 / (n : ℝ) ^ k := by
  have hS : HasSum (fun n : ℕ => 2 * (1 / (n : ℝ) ^ k)) (2 * ∑' n : ℕ, 1 / (n : ℝ) ^ k) :=
    (Real.summable_one_div_nat_pow.mpr hk).hasSum.mul_left 2
  have h := (hasSum_one_div_nat_pow_mul_fourier hk hx).norm_le_of_bounded hS fun n => by
    rw [norm_mul, mul_comm]
    have hn : ‖(1 : ℂ) / (n : ℂ) ^ k‖ = 1 / (n : ℝ) ^ k := by simp
    rw [hn]
    gcongr
    refine (norm_add_le _ _).trans ?_
    norm_num [Circle.norm_coe]
  have hn : ‖-(2 * π * Complex.I) ^ k / k ! * (bernoulliFun k x : ℂ)‖ =
      |bernoulliFun k x| * ((2 * π) ^ k / k !) := by
    simp [abs_of_pos Real.pi_pos, mul_comm]
  rw [hn, ← le_div_iff₀ (by positivity)] at h
  exact h.trans_eq (by field_simp)

/-- For every `k : ℕ` and `x ∈ [0, 1]`, `|B_k(x)| ≤ π² / 3 · k! / (2π)^k`, with `k!` cast to
`ℝ`. For `2 ≤ k` this follows from `TauCeti.abs_bernoulliFun_le_mul_tsum` and
`∑_{n : ℕ} 1 / n^k ≤ π² / 6`. The constant is attained at `k = 2`, `x = 0`, where both sides
are `1 / 6`. -/
theorem abs_bernoulliFun_le_pi_sq_div_three_mul_factorial_div (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : |bernoulliFun k x| ≤ π ^ 2 / 3 * k ! / (2 * π) ^ k := by
  obtain _ | _ | k := k
  · have : (3 : ℝ) ^ 2 ≤ π ^ 2 := by gcongr; exact Real.pi_gt_three.le
    simp only [bernoulliFun_zero, abs_one, Nat.factorial_zero, Nat.cast_one, pow_zero]
    linarith
  · have h : 1 / 2 ≤ π ^ 2 / 3 * (1 : ℕ)! / (2 * π) ^ 1 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [Real.pi_gt_three]
    rw [bernoulliFun_one, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  · have hle : ∑' n : ℕ, 1 / (n : ℝ) ^ (k + 2) ≤ π ^ 2 / 6 := by
      refine hasSum_le (fun n => ?_) (Real.summable_one_div_nat_pow.mpr (by omega)).hasSum
        hasSum_zeta_two
      rcases n.eq_zero_or_pos with rfl | hn
      · simp
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        gcongr
        omega
    refine (abs_bernoulliFun_le_mul_tsum (by omega) hx).trans ?_
    calc 2 * (k + 2)! / (2 * π) ^ (k + 2) * ∑' n : ℕ, 1 / (n : ℝ) ^ (k + 2)
        ≤ 2 * (k + 2)! / (2 * π) ^ (k + 2) * (π ^ 2 / 6) := by gcongr
      _ = π ^ 2 / 3 * (k + 2)! / (2 * π) ^ (k + 2) := by ring

/-- For every `k : ℕ` and `x ∈ [0, 1]`, `|B_k(x)| ≤ 4 · k! / (2π)^k`, with `k!` cast to `ℝ`:
the bound `TauCeti.abs_bernoulliFun_le_pi_sq_div_three_mul_factorial_div` with `π² / 3 < 4`. -/
theorem abs_bernoulliFun_le_four_mul_factorial_div (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : |bernoulliFun k x| ≤ 4 * k ! / (2 * π) ^ k := by
  refine (abs_bernoulliFun_le_pi_sq_div_three_mul_factorial_div k hx).trans ?_
  have : π ^ 2 < 3.15 ^ 2 := by gcongr; exact Real.pi_lt_d2
  gcongr
  linarith

/-- For every `k : ℕ` and rational `x ∈ [0, 1]`, the Bernoulli polynomial over `ℚ` satisfies
`|B_k(x)| ≤ 4 · k! / (2π)^k`, with the value cast to `ℝ`. -/
theorem abs_eval_bernoulli_le_four_mul_factorial_div (k : ℕ) {x : ℚ}
    (hx : x ∈ Set.Icc (0 : ℚ) 1) :
    |(((Polynomial.bernoulli k).eval x : ℚ) : ℝ)| ≤ 4 * k ! / (2 * π) ^ k := by
  rw [← bernoulliFun_ratCast]
  exact abs_bernoulliFun_le_four_mul_factorial_div k ⟨mod_cast hx.1, mod_cast hx.2⟩

/-- **Uniform bound on Bernoulli polynomials at `n / N`.** For natural numbers `n ≤ N`,
`|B_k(n / N)| ≤ 4 · k! / (2π)^k`. Only `n ≤ N` for `N ≠ 0` is needed, since `n / 0 = 0`. -/
theorem abs_eval_bernoulli_natCast_div_le_four_mul_factorial_div (k : ℕ) {n N : ℕ}
    (h : N ≠ 0 → n ≤ N) :
    |(((Polynomial.bernoulli k).eval ((n : ℚ) / N) : ℚ) : ℝ)| ≤ 4 * k ! / (2 * π) ^ k := by
  refine abs_eval_bernoulli_le_four_mul_factorial_div k ⟨by positivity, ?_⟩
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · exact div_le_one_of_le₀ (mod_cast h hN) (Nat.cast_nonneg N)

end TauCeti
