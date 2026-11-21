/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.StepCorrection
import TauCeti.Analysis.LaplaceTransform.UniformStep
import TauCeti.Analysis.SpecialFunctions.Log.Base
import TauCeti.NumberTheory.LSeries.BoundaryConvergence.Endpoint

/-!
# Block-constant Dirichlet series and uniform step transforms

For an integer base `b > 1` and a sequence `c : ℕ → ℂ`, the `b`-adic block-constant sequence
`a n = c (Nat.log b n)` (`n ≥ 1`, `a 0 = 0`) satisfies `Nat.log b ⌊exp t⌋₊ = ⌊t / log b⌋₊`
for `0 ≤ t` (`Real.natFloor_logb_eq_natLog_natFloor`). Consequently:

* when `c` is bounded and `0 < re z`, `LSeries a (z + 1) + stepCorrection a z` equals
  `(∫ u in 0..log b, exp (-z * u)) * ∑' k, c k * exp (-log b * z) ^ k`
  (`LSeries_natLog_add_stepCorrection`);
* at cutoffs `b ^ K - 1`, the ordered harmonic partial sum plus the step correction at `z = 0`
  equals `log b * ∑ k ∈ range K, c k` (`sum_Icc_natLog_div_add_stepCorrectionTerm`).
-/

public section

open MeasureTheory Set Complex
open scoped Interval

namespace TauCeti.LSeries

private theorem natLog_floor_exp_eq (b : ℕ) (c : ℕ → ℂ) {t : ℝ} (ht : 0 ≤ t) :
    (if ⌊Real.exp t⌋₊ = 0 then (0 : ℂ) else c (Nat.log b ⌊Real.exp t⌋₊)) =
      c ⌊t / Real.log b⌋₊ := by
  rw [ite_eq_right (Nat.floor_pos.mpr (Real.one_le_exp ht)).ne',
    ← Real.natFloor_logb_eq_natLog_natFloor b (Real.exp_nonneg t), Real.logb, Real.log_exp]

/-- **Laplace–Dirichlet bridge for `b`-adic block coefficients.** For an integer base `b > 1`,
a bounded sequence `c : ℕ → ℂ`, and `0 < re z`, the shifted Dirichlet series of
`n ↦ if n = 0 then 0 else c (Nat.log b n)` plus its step correction equals
`(∫ u in 0..log b, exp (-z * u)) * ∑' k, c k * exp (-log b * z) ^ k`. -/
theorem LSeries_natLog_add_stepCorrection {b : ℕ} (hb : 1 < b) {c : ℕ → ℂ} {M : ℝ}
    (hbound : ∀ n, ‖c n‖ ≤ M) {z : ℂ} (hz : 0 < z.re) :
    LSeries (fun n ↦ if n = 0 then 0 else c (Nat.log b n)) (z + 1) +
        stepCorrection (fun n ↦ if n = 0 then 0 else c (Nat.log b n)) z =
      (∫ u in (0 : ℝ)..Real.log b, cexp (-z * u)) *
        ∑' k, c k * cexp (-(Real.log b : ℂ) * z) ^ k := by
  have habound : ∀ n, 1 ≤ n → ‖(if n = 0 then 0 else c (Nat.log b n))‖ ≤ M := by
    intro n hn
    simp [Nat.one_le_iff_ne_zero.mp hn, hbound]
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  rw [← integral_floor_exp_mul_cexp_neg_mul habound hz,
    ← integral_floor_div_mul_cexp_neg_mul hbound hlogb hz]
  refine setIntegral_congr_fun measurableSet_Ici fun t ht ↦ ?_
  rw [natLog_floor_exp_eq b c ht]

/-- **Partial-sum identity for `b`-adic block coefficients at powers of `b`.** For an integer
base `b > 1`, any sequence `c : ℕ → ℂ`, and every `K : ℕ`, the ordered harmonic partial sum up to
`b ^ K - 1` plus the corresponding partial sum of the step correction at `z = 0` equals
`log b * ∑ k ∈ range K, c k`. -/
theorem sum_Icc_natLog_div_add_stepCorrectionTerm {b : ℕ} (hb : 1 < b) (c : ℕ → ℂ) (K : ℕ) :
    (∑ n ∈ Finset.Icc 1 (b ^ K - 1), c (Nat.log b n) / (n : ℂ)) +
        ∑ n ∈ Finset.range (b ^ K),
          stepCorrectionTerm (fun n ↦ if n = 0 then 0 else c (Nat.log b n)) n 0 =
      (Real.log b : ℂ) * ∑ k ∈ Finset.range K, c k := by
  set a : ℕ → ℂ := fun n ↦ if n = 0 then 0 else c (Nat.log b n)
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb)
  have hpow_pos : 1 ≤ b ^ K := Nat.one_le_pow K b (by omega)
  have hlog_eq : Real.log (((b ^ K - 1 : ℕ) : ℝ) + 1) = (K : ℝ) * Real.log b := by
    have hcast : (((b ^ K - 1 : ℕ) : ℝ) + 1) = (b : ℝ) ^ K := by
      exact_mod_cast Nat.sub_add_cancel hpow_pos
    rw [hcast, Real.log_pow]
  -- Evaluate the integral of `t ↦ a ⌊exp t⌋₊` over `[0, K * log b]` in two ways.
  have hL := intervalIntegral_floor_exp_mul_cexp_neg_mul_log_succ a (b ^ K - 1) 0
  simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one, zero_add] at hL
  rw [hlog_eq, Nat.sub_add_cancel hpow_pos, Finset.sum_add_distrib] at hL
  have hR := intervalIntegral_floor_div_mul_cexp_neg_mul c hlogb K 0
  simp only [neg_zero, zero_mul, Complex.exp_zero, mul_one,
    intervalIntegral.integral_const, sub_zero] at hR
  have hint_eq : ∫ t in (0 : ℝ)..((K : ℝ) * Real.log b), a ⌊Real.exp t⌋₊ =
      ∫ t in (0 : ℝ)..((K : ℝ) * Real.log b), c ⌊t / Real.log b⌋₊ := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le (by positivity)] at ht
    exact natLog_floor_exp_eq b c ht.1
  have hterm : ∑ n ∈ Finset.range (b ^ K), LSeries.term a 1 n =
      ∑ n ∈ Finset.Icc 1 (b ^ K - 1), c (Nat.log b n) / (n : ℂ) := by
    rw [← Nat.sub_add_cancel hpow_pos, sum_range_add_one_LSeries_term_one]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    simp [a, Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1]
  rw [← hterm, ← hL, hint_eq, hR]
  simp [Complex.real_smul]

end TauCeti.LSeries
