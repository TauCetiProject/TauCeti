/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Bounds for the positive part of the logarithm

On `[0, ∞)` the positive part of the logarithm lies below the line `x ↦ exp (-1) * x`, which is
tangent to `log` at `x = e`. Integrated against a probability measure, this linear bound is what
controls the mean of `log⁺` by `log⁺` of the mean up to the additive constant `exp (-1)`.

The positive part of the logarithm is `1`-Lipschitz on all of `ℝ`: it is `log (max 1 |x|)`, and
`log` is `1`-Lipschitz on `[1, ∞)`.

## Main results

* `Real.posLog_le_exp_neg_one_mul`: `log⁺ x ≤ exp (-1) * x` for `0 ≤ x`.
* `Real.lipschitzWith_posLog`: `|log⁺ x - log⁺ y| ≤ |x - y|`.
-/

public section

namespace Real

/-- The positive part of the logarithm is at most `exp (-1)` times its argument on `[0, ∞)`:
the line through the origin tangent to `log` touches it at `x = e`. -/
theorem posLog_le_exp_neg_one_mul {x : ℝ} (hx : 0 ≤ x) : log⁺ x ≤ exp (-1) * x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  refine max_le (by positivity) ?_
  have h := mul_exp_neg_le_exp_neg_one (log x)
  rwa [exp_neg, exp_log hx, ← div_eq_mul_inv, div_le_iff₀ hx] at h

/-- The positive part of the logarithm is `1`-Lipschitz on `ℝ`. -/
theorem lipschitzWith_posLog : LipschitzWith 1 log⁺ := by
  -- On `[1, ∞)` the logarithm grows by at most the growth of its argument.
  have key {a b : ℝ} (hb : 1 ≤ b) (hba : b ≤ a) : |log a - log b| ≤ |a - b| := by
    have hb0 : 0 < b := by linarith
    rw [abs_of_nonneg (sub_nonneg.2 (log_le_log hb0 hba)), abs_of_nonneg (sub_nonneg.2 hba),
      ← log_div (by linarith) hb0.ne']
    calc log (a / b) ≤ a / b - 1 := log_le_sub_one_of_pos (div_pos (by linarith) hb0)
      _ = (a - b) / b := by field_simp
      _ ≤ a - b := div_le_self (by linarith) hb
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_eq, dist_eq, ← posLog_abs x, ← posLog_abs y,
    posLog_eq_log_max_one (abs_nonneg x), posLog_eq_log_max_one (abs_nonneg y)]
  have hmax : |max 1 (|x|) - max 1 (|y|)| ≤ |x - y| := by
    rw [max_comm 1 |x|, max_comm 1 |y|]
    exact (abs_max_sub_max_le_abs _ _ _).trans (abs_abs_sub_abs_le _ _)
  refine le_trans ?_ hmax
  rcases le_total (max 1 |y|) (max 1 |x|) with h | h
  · exact key (le_max_left _ _) h
  · rw [abs_sub_comm, abs_sub_comm (max 1 |x|)]
    exact key (le_max_left _ _) h

end Real
