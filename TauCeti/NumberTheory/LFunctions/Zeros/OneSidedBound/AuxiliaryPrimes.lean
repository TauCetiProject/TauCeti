/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith

/-!
# Logarithmic window bounds for the principal level

To choose more split primes than the class number of the quadratic field, use disjoint
windows of width `W` in `[10 log b, 11 log b]`, where `W^6 ≤ log b ≤ W^6 + 1`.
This file proves that the windows fit and that their left endpoints lie in `[W, W^7]`.
It does not assert that the windows contain primes.

The interval and the scale are from `New.Parameters.IsLargeScale.exists_isAdmissibleData`
in `New/Reduction/Data/Existence.lean` of lsernau/grh-lean at
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Filter

namespace TauCeti.OneSidedBound

/-- For large `W` and `W^6 ≤ L ≤ W^6 + 1`, the interval `[10 * L, 11 * L]` lies in
`[W, W^7]` and can hold `n` windows of width `W` with left endpoints spaced by `2 * W`.
For the principal level take `L = log b` and `n` one more than the class number. -/
theorem eventually_log_window_bounds (n : ℕ) :
    ∀ᶠ W : ℝ in atTop, ∀ L : ℝ, W ^ 6 ≤ L → L ≤ W ^ 6 + 1 →
      1 ≤ W ∧ W ≤ 10 * L ∧ 10 * L + 2 * n * W ≤ 11 * L ∧ 11 * L ≤ W ^ 7 := by
  filter_upwards [eventually_ge_atTop (max 22 (2 * n : ℝ))] with W hW L hlo hhi
  have h22 := (le_max_left _ _).trans hW
  have hn := (le_max_right _ _).trans hW
  have h1 : 1 ≤ W := by linarith
  have hW0 : 0 ≤ W := zero_le_one.trans h1
  have hW6 : W ≤ W ^ 6 := by simpa using pow_le_pow_right₀ h1 (by decide : 1 ≤ 6)
  refine ⟨h1, by linarith, ?_, ?_⟩
  · have hW2 : W ^ 2 ≤ W ^ 6 := pow_le_pow_right₀ h1 (by decide)
    nlinarith [mul_le_mul_of_nonneg_right hn hW0]
  · calc
      11 * L ≤ 22 * W ^ 6 := by linarith
      _ ≤ W ^ 7 := by simpa [pow_succ, mul_comm] using
        mul_le_mul_of_nonneg_right h22 (pow_nonneg hW0 6)

end TauCeti.OneSidedBound
