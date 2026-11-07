/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Zeros and logarithmic derivatives of weighted Euler factors

For a positive base `q > 1` and `‖a‖ ≤ 1`, the factor `1 - a q^(-s)` is nonzero
on `Re s > 0`. When `‖a‖ = 1`, all its zeros have real part zero.
For `q ≥ 2` and `Re s ≥ 1` its logarithmic derivative has norm at most `log q`.
These estimates control finite Euler corrections uniformly in the character.
-/

public section

open Complex Real
namespace Complex

/-- The logarithmic derivative of a weighted exponential Euler factor, with total division. -/
theorem logDeriv_one_sub_mul_cpow_neg {q : ℂ} (hq : q ≠ 0) (a s : ℂ) :
    logDeriv (fun z : ℂ ↦ 1 - a * q ^ (-z)) s =
      a * q ^ (-s) * log q / (1 - a * q ^ (-s)) := by
  have hd := (((hasDerivAt_neg s).const_cpow (Or.inl hq)).const_mul a).const_sub 1
  rw [logDeriv_apply, hd.deriv]
  ring

/-- A weighted Euler factor with unit-modulus coefficient can vanish only on the imaginary axis. -/
theorem re_eq_zero_of_one_sub_mul_ofReal_cpow_neg_eq_zero {q : ℝ} (hq : 1 < q)
    {a s : ℂ} (ha : ‖a‖ = 1) (hz : 1 - a * (q : ℂ) ^ (-s) = 0) : s.re = 0 := by
  have he := congrArg norm (sub_eq_zero.mp hz)
  rw [norm_one, norm_mul, ha, one_mul,
    norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < q), neg_re] at he
  have hp : q ^ (-s.re) = q ^ (0 : ℝ) := by simpa using he.symm
  have h := (Real.rpow_right_inj (by linarith : 0 < q) (ne_of_gt hq)).mp hp
  linarith

/-- An Euler factor with coefficient of norm at most one is nonzero in the open right half-plane. -/
theorem one_sub_mul_ofReal_cpow_neg_ne_zero {q : ℝ} (hq : 1 < q)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : 1 - a * (q : ℂ) ^ (-s) ≠ 0 := by
  have hq0 : 0 < q := by linarith
  have hpow : ‖(q : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos hq0, neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by linarith)
  intro hz
  have he := congrArg norm (sub_eq_zero.mp hz)
  rw [norm_one, norm_mul] at he
  have hle := mul_le_mul_of_nonneg_right ha (norm_nonneg ((q : ℂ) ^ (-s)))
  nlinarith

/-- For base at least two and real part at least one, the factor logarithmic derivative has norm
at most the logarithm of its base. -/
theorem norm_logDeriv_one_sub_mul_ofReal_cpow_neg_le {q : ℝ} (hq : 2 ≤ q)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : 1 ≤ s.re) :
    ‖logDeriv (fun z : ℂ ↦ 1 - a * (q : ℂ) ^ (-z)) s‖ ≤ Real.log q := by
  have hq0 : 0 < q := by linarith
  have hlog : ‖log (q : ℂ)‖ = Real.log q := by
    rw [← ofReal_log hq0.le, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith))]
  have hpow : ‖(q : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_cpow_eq_rpow_re_of_pos hq0, neg_re]
    calc
      q ^ (-s.re) ≤ q ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = q⁻¹ := Real.rpow_neg_one q
      _ ≤ 1 / 2 := by simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hq
  have hterm : ‖a * (q : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using hpow)
  have hden : (1 / 2 : ℝ) ≤ ‖1 - a * (q : ℂ) ^ (-s)‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (a * (q : ℂ) ^ (-s))
    rw [norm_one] at ht
    linarith
  rw [logDeriv_one_sub_mul_cpow_neg (by exact_mod_cast hq0.ne'), norm_div, norm_mul, hlog]
  apply (div_le_iff₀ (by linarith : 0 < ‖1 - a * (q : ℂ) ^ (-s)‖)).mpr
  have hlog0 : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hterm hlog0,
    mul_le_mul_of_nonneg_left hden hlog0]

end Complex
