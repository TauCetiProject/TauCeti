/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Real

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
  have hlog : Real.log ρ ≠ 0 := (Real.log_neg hρ₀ hρ₁).ne
  -- Eventually `k n ≥ ((a + 2) / -log ρ) * log n`, so the terms are at most `n ^ (-2)`.
  have hbound : ∀ᶠ n : ℕ in atTop, ‖(n : ℝ) ^ a * r ^ k n‖ ≤ (n : ℝ) ^ (-2 : ℝ) := by
    filter_upwards [hk.eventually_ge_atTop ((a + 2) / -Real.log ρ), eventually_gt_atTop 1]
      with n hkn hn
    have hn₁ : (1 : ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ (Real.log_pos hn₁)] at hkn
    have hrate : (a + 2) / -Real.log ρ * Real.log ρ = -(a + 2) := by
      field_simp
    rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_natCast (n : ℝ) a]
    calc (n : ℝ) ^ (a : ℝ) * r ^ k n ≤ (n : ℝ) ^ (a : ℝ) * ρ ^ k n := by
          gcongr
          exact le_max_left r 2⁻¹
      _ ≤ (n : ℝ) ^ (-2 : ℝ) :=
        rpow_mul_pow_le_rpow_of_log_le hn₁.le hρ₀ hρ₁.le hkn (by rw [hrate]; linarith)
  exact (Real.summable_nat_rpow.2 (by norm_num)).of_norm_bounded_eventually_nat hbound

end TauCeti
