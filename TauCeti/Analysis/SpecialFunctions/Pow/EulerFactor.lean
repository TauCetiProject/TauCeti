/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Zeros and logarithmic derivatives of weighted Euler factors

For a base `q > 1` and `‖a‖ = 1`, every zero of the factor `1 - a q^(-s)` has real part zero.
For `q ≥ 2` and `Re s ≥ 1` its logarithmic derivative has norm at most `log q`.
These estimates control finite Euler corrections uniformly in the character. The unweighted
factor also has the exact logarithmic derivative `log q / (q ^ s - 1)`; at a real argument
and a nonnegative real base, its real part is `Real.log q / (q ^ σ - 1)`.
-/

public section

open Complex Real
namespace Complex

/-- The logarithmic derivative of a weighted exponential Euler factor, with total division. -/
theorem logDeriv_one_sub_mul_cpow_neg {q : ℂ} (a s : ℂ) :
    logDeriv (fun z : ℂ ↦ 1 - a * q ^ (-z)) s =
      a * q ^ (-s) * log q / (1 - a * q ^ (-s)) := by
  rw [logDeriv_apply, deriv_const_sub, deriv_const_mul_field,
    Complex.deriv_const_cpow differentiable_neg.differentiableAt, deriv_neg]
  ring

/-- A zero base is allowed for every complex coefficient and argument, with total division. -/
example (a s : ℂ) : logDeriv (fun z : ℂ ↦ 1 - a * (0 : ℂ) ^ (-z)) s = 0 := by
  simpa only [log_zero, mul_zero, zero_div] using
    logDeriv_one_sub_mul_cpow_neg (q := 0) a s

/-- An unweighted Euler factor has logarithmic derivative `log q / (q ^ s - 1)`,
with total division even when the factor vanishes. -/
theorem logDeriv_one_sub_cpow_neg (q s : ℂ) :
    logDeriv (fun z : ℂ ↦ 1 - q ^ (-z)) s = log q / (q ^ s - 1) := by
  have h := logDeriv_one_sub_mul_cpow_neg (q := q) 1 s
  simp only [one_mul] at h
  rw [h, cpow_neg]
  by_cases hq : q = 0
  · simp only [hq, log_zero, mul_zero, zero_div]
  by_cases hpow : q ^ s = 1
  · simp only [hpow, inv_one, sub_self, div_zero]
  · field_simp [cpow_ne_zero_iff.mpr (.inl hq), sub_ne_zero.mpr hpow]

/-- At a real argument, an unweighted Euler factor with nonnegative real base has the real
logarithmic derivative `log q / (q ^ σ - 1)`, with total division. -/
theorem re_logDeriv_one_sub_ofReal_cpow_neg {q : ℝ} (hq : 0 ≤ q) (σ : ℝ) :
    (logDeriv (fun z : ℂ ↦ 1 - (q : ℂ) ^ (-z)) (σ : ℂ)).re =
      Real.log q / (q ^ σ - 1) := by
  rw [logDeriv_one_sub_cpow_neg,
    ← Complex.ofReal_cpow hq, ← Complex.ofReal_log hq, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]

-- Base zero is included at every real exponent, with total division also at exponent zero.
example (σ : ℝ) :
    (logDeriv (fun z : ℂ ↦ 1 - (0 : ℂ) ^ (-z)) (σ : ℂ)).re = 0 := by
  simpa only [Complex.ofReal_zero, Real.log_zero, zero_div] using
    re_logDeriv_one_sub_ofReal_cpow_neg (q := 0) (le_refl 0) σ

/-- A weighted Euler factor with unit-modulus coefficient can vanish only on the imaginary axis. -/
theorem re_eq_zero_of_one_sub_mul_ofReal_cpow_neg_eq_zero {q : ℝ} (hq : 1 < q)
    {a s : ℂ} (ha : ‖a‖ = 1) (hz : 1 - a * (q : ℂ) ^ (-s) = 0) : s.re = 0 := by
  have he := congrArg norm (sub_eq_zero.mp hz)
  rw [norm_one, norm_mul, ha, one_mul,
    norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < q), neg_re] at he
  have hp : q ^ (-s.re) = q ^ (0 : ℝ) := by simpa using he.symm
  have h := (Real.rpow_right_inj (by linarith : 0 < q) (ne_of_gt hq)).mp hp
  linarith

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
    exact Real.rpow_neg_le_half hq hs
  have hterm : ‖a * (q : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using hpow)
  have hden : (1 / 2 : ℝ) ≤ ‖1 - a * (q : ℂ) ^ (-s)‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (a * (q : ℂ) ^ (-s))
    rw [norm_one] at ht
    linarith
  rw [logDeriv_one_sub_mul_cpow_neg, norm_div, norm_mul, hlog]
  apply (div_le_iff₀ (by linarith : 0 < ‖1 - a * (q : ℂ) ^ (-s)‖)).mpr
  have hlog0 : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hterm hlog0,
    mul_le_mul_of_nonneg_left hden hlog0]

end Complex
