/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Upper bounds on logarithm-weighted harmonic sums

From Mathlib's harmonic-number bound `harmonic n ≤ 1 + log n` (`harmonic_le_one_add_log`), the
tail sum `∑ k ∈ Ioc 1 n, (k : ℝ)⁻¹` is at most `log n`, so bounding `log k ≤ log n` yields
`∑_{k=1}^n (log k) / k ≤ (log n)²` for every natural number `n`.

Near the line `σ = 1`, for any `c ≥ 0` and `σ ≥ 1 - c / log n`, each term satisfies
`k^{-σ} ≤ k^{-1} * n^{c / log n} = exp c / k`, giving
`∑_{k=1}^n (log k) k^{-σ} ≤ exp c * (log n)²` for every `n : ℕ` (the cases `n = 0, 1` reduce to
`0 ≤ 0`). These bounds control the finite initial Dirichlet polynomial of `L'(σ, χ)` after
partial summation up to the level `N`.

## Main results

* `Nat.sum_Icc_log_div_le_log_sq`: `∑ k ∈ Finset.Icc 1 n, Real.log k / k ≤ (Real.log n) ^ 2`
  for all `n : ℕ`.
* `Nat.sum_Icc_log_mul_rpow_neg_le_exp_mul_log_sq`:
  `∑ k ∈ Finset.Icc 1 n, Real.log k * k ^ (-σ) ≤ Real.exp c * (Real.log n) ^ 2` for all `n : ℕ`,
  `0 ≤ c`, and `1 - c / Real.log n ≤ σ`.
-/

public section

open Finset

namespace Nat

/-- For every natural number `n`, `∑_{k=1}^n (log k) / k ≤ (log n)²`. -/
theorem sum_Icc_log_div_le_log_sq (n : ℕ) :
    ∑ k ∈ Icc 1 n, Real.log k / (k : ℝ) ≤ Real.log n ^ 2 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hn' : (1 : ℝ) ≤ n := mod_cast hn
  have hsplit : ∑ k ∈ Icc 1 n, Real.log k / (k : ℝ) =
      ∑ k ∈ Ioc 1 n, Real.log k * (k : ℝ)⁻¹ := by
    rw [← sum_erase_add (Icc 1 n) _ (left_mem_Icc.mpr hn), Nat.cast_one, Real.log_one,
      zero_div, add_zero, Icc_erase_left]
    refine sum_congr rfl fun k _ ↦ div_eq_mul_inv _ _
  have hharm : ∑ k ∈ Ioc 1 n, (k : ℝ)⁻¹ ≤ Real.log n := by
    have hh := harmonic_le_one_add_log n
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
    rw [← sum_erase_add (Icc 1 n) _ (left_mem_Icc.mpr hn), Nat.cast_one, inv_one,
      Icc_erase_left] at hh
    linarith
  rw [hsplit]
  calc
    ∑ k ∈ Ioc 1 n, Real.log k * (k : ℝ)⁻¹
      ≤ ∑ k ∈ Ioc 1 n, Real.log n * (k : ℝ)⁻¹ := by
        refine sum_le_sum fun k hk ↦ mul_le_mul_of_nonneg_right ?_ (by positivity)
        have hk' := mem_Ioc.mp hk
        exact Real.log_le_log (by exact_mod_cast (by omega : 0 < k))
          (by exact_mod_cast hk'.2)
    _ = Real.log n * ∑ k ∈ Ioc 1 n, (k : ℝ)⁻¹ := (mul_sum _ _ _).symm
    _ ≤ Real.log n * Real.log n := mul_le_mul_of_nonneg_left hharm (Real.log_nonneg hn')
    _ = Real.log n ^ 2 := (sq _).symm

/-- For every `n : ℕ`, `0 ≤ c`, and `σ ≥ 1 - c / log n`,
`∑_{k=1}^n (log k) k^{-σ} ≤ exp c * (log n)²`. -/
theorem sum_Icc_log_mul_rpow_neg_le_exp_mul_log_sq (n : ℕ) {c σ : ℝ} (hc : 0 ≤ c)
    (hσ : 1 - c / Real.log n ≤ σ) :
    ∑ k ∈ Icc 1 n, Real.log k * (k : ℝ) ^ (-σ) ≤ Real.exp c * Real.log n ^ 2 := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;> simp
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans hn1
  have hlog_pos : 0 < Real.log n := Real.log_pos hn1
  have hn_pow : (n : ℝ) ^ (c / Real.log n) = Real.exp c := by
    rw [Real.rpow_def_of_pos hn0, mul_div_cancel₀ _ hlog_pos.ne']
  calc
    ∑ k ∈ Icc 1 n, Real.log k * (k : ℝ) ^ (-σ)
      ≤ ∑ k ∈ Icc 1 n, Real.exp c * (Real.log k / k) := by
        refine sum_le_sum fun k hk ↦ ?_
        have hk1 : (1 : ℝ) ≤ k := mod_cast (mem_Icc.mp hk).1
        have hkn : (k : ℝ) ≤ n := mod_cast (mem_Icc.mp hk).2
        have hk0 : (0 : ℝ) < k := zero_lt_one.trans_le hk1
        have hrpow : (k : ℝ) ^ (-σ) ≤ Real.exp c / k := by
          calc
            (k : ℝ) ^ (-σ) ≤ (k : ℝ) ^ (-1 + c / Real.log n) :=
              Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)
            _ = (k : ℝ) ^ (-1 : ℝ) * (k : ℝ) ^ (c / Real.log n) := Real.rpow_add hk0 _ _
            _ ≤ (k : ℝ)⁻¹ * (n : ℝ) ^ (c / Real.log n) := by
              rw [Real.rpow_neg_one]
              exact mul_le_mul_of_nonneg_left
                (Real.rpow_le_rpow hk0.le hkn (div_nonneg hc hlog_pos.le)) (by positivity)
            _ = Real.exp c / k := by rw [hn_pow, div_eq_mul_inv, mul_comm]
        calc
          Real.log k * (k : ℝ) ^ (-σ) ≤ Real.log k * (Real.exp c / k) :=
            mul_le_mul_of_nonneg_left hrpow (Real.log_nonneg hk1)
          _ = Real.exp c * (Real.log k / k) := by ring
    _ = Real.exp c * ∑ k ∈ Icc 1 n, Real.log k / (k : ℝ) := (mul_sum _ _ _).symm
    _ ≤ Real.exp c * Real.log n ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_Icc_log_div_le_log_sq n) (Real.exp_nonneg c)

end Nat
