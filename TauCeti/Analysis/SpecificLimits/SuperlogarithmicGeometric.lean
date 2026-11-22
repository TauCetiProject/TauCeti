/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries

/-!
# Geometric series with superlogarithmic exponents

If `0 ≤ r < 1` and the exponents `k n` grow faster than `log n`, then `r ^ k n` decays faster than
every power of `n`, so `n ^ a * r ^ k n` is summable for every `a`. Summability of such sequences
is what turns a moment bound of growing order into a summable family of tail probabilities, as
in the trace method for the largest eigenvalue of a random matrix.
-/

public section

open Filter

namespace TauCeti

/-- If `0 ≤ r < 1` and the exponents `k n` grow faster than `log n`, then `n ^ a * r ^ k n` is
summable for every natural `a`. -/
theorem summable_pow_mul_pow_of_tendsto_div_log_atTop {k : ℕ → ℕ}
    (hk : Tendsto (fun n ↦ (k n : ℝ) / Real.log n) atTop atTop) (a : ℕ) {r : ℝ} (hr₀ : 0 ≤ r)
    (hr₁ : r < 1) :
    Summable fun n : ℕ ↦ (n : ℝ) ^ a * r ^ k n := by
  -- Replace `r` by a positive ratio `ρ < 1` with `r ≤ ρ`.
  set ρ := max r 2⁻¹
  have hρ₀ : 0 < ρ := lt_max_of_lt_right (by norm_num)
  have hρ₁ : ρ < 1 := max_lt hr₁ (by norm_num)
  have hlog : 0 < -Real.log ρ := neg_pos.2 (Real.log_neg hρ₀ hρ₁)
  -- Eventually `ρ ^ k n ≤ n⁻⁽ᵃ⁺²⁾`, so the terms are at most `n⁻²`.
  have hbound : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ) ^ a * r ^ k n‖ ≤ ((n : ℝ) ^ 2)⁻¹ := by
    filter_upwards [hk.eventually_ge_atTop ((a + 2) / -Real.log ρ), eventually_gt_atTop 1]
      with n hkn hn
    have hn₀ : (0 : ℝ) < n := by exact_mod_cast zero_lt_one.trans hn
    have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    have hexp : (k n : ℝ) * Real.log ρ ≤ -((a + 2) * Real.log n) := by
      rw [div_le_div_iff₀ hlog hlogn] at hkn
      linarith
    have hρpow : ρ ^ k n ≤ ((n : ℝ) ^ (a + 2))⁻¹ := by
      rw [← Real.exp_log (pow_pos hρ₀ _), Real.log_pow,
        ← Real.exp_log (inv_pos.2 (pow_pos hn₀ (a + 2))), Real.log_inv, Real.log_pow]
      exact Real.exp_le_exp.2 (by push_cast; linarith)
    rw [Real.norm_of_nonneg (by positivity)]
    calc (n : ℝ) ^ a * r ^ k n ≤ (n : ℝ) ^ a * ((n : ℝ) ^ (a + 2))⁻¹ := by
          gcongr
          exact (pow_le_pow_left₀ hr₀ (le_max_left r 2⁻¹) _).trans hρpow
      _ = ((n : ℝ) ^ 2)⁻¹ := by
        rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_pos hn₀ a).ne', one_mul]
  exact (Real.summable_nat_pow_inv.2 one_lt_two).of_norm_bounded_eventually_nat hbound

end TauCeti
