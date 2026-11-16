/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Elementary numerical bounds on the real logarithm

From `log x ≤ x - 1` for `x > 0` (`Real.log_le_sub_one_of_pos`) applied at `x = 2` and `x / 2`,
one obtains `log 4 = 2 log 2 ≤ 2` and `log x / x ≤ 1 / 2` for every real `x ≥ 0` (holding at
`x = 0` via `0 / 0 = 0`). The first compares explicit prime-counting constants involving `log 4`
with rational constants, and the second bounds the contribution `log p / p` of a single prime at a
real cutoff `x` when passing between inclusive and strict prime sums. Finally, monotonicity of
the logarithm bounds `|log x|` by `|log δ| + log B` on an interval `[δ, B]` with `0 < δ` and
`1 ≤ B`.

## Main results

* `Real.log_four_le_two`: `log 4 ≤ 2`.
* `Real.log_div_self_le_half`: `log x / x ≤ 1 / 2` for every nonnegative real `x`.
* `Real.abs_log_le_of_mem_Icc`: `|log x| ≤ |log δ| + log B` on `[δ, B]`, for `0 < δ` and `1 ≤ B`.
-/

public section

namespace Real

/-- The natural logarithm of `4` is at most `2`. -/
theorem log_four_le_two : log 4 ≤ 2 := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, log_pow]
  norm_num
  linarith [log_le_sub_one_of_pos zero_lt_two]

/-- For every nonnegative real `x`, `log x / x ≤ 1 / 2` (holding at `x = 0` via `0 / 0 = 0`). -/
theorem log_div_self_le_half {x : ℝ} (hx : 0 ≤ x) : log x / x ≤ 1 / 2 := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · norm_num
  have h := log_le_sub_one_of_pos (half_pos hx)
  rw [log_div hx.ne' two_ne_zero] at h
  rw [div_le_iff₀ hx]
  linarith [log_le_sub_one_of_pos zero_lt_two]

/-- On an interval `[δ, B]` with `0 < δ` and `1 ≤ B`, the logarithm is bounded in absolute
value by `|log δ| + log B`. -/
theorem abs_log_le_of_mem_Icc {δ B x : ℝ} (hδ : 0 < δ) (hB : 1 ≤ B) (hx : x ∈ Set.Icc δ B) :
    |log x| ≤ |log δ| + log B := by
  have h1 : log δ ≤ log x := log_le_log hδ hx.1
  have h2 : log x ≤ log B := log_le_log (hδ.trans_le hx.1) hx.2
  have h3 : 0 ≤ log B := log_nonneg hB
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [neg_abs_le (log δ), le_abs_self (log δ)]

end Real
