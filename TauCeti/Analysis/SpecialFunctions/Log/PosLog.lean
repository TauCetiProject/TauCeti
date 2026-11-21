/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A linear upper bound for the positive part of the logarithm

On `[0, ∞)` the positive part of the logarithm lies below the line `x ↦ exp (-1) * x`, which is
tangent to `log` at `x = e`. Integrated against a probability measure, this linear bound is what
controls the mean of `log⁺` by `log⁺` of the mean up to the additive constant `exp (-1)`.

## Main results

* `Real.posLog_le_exp_neg_one_mul`: `log⁺ x ≤ exp (-1) * x` for `0 ≤ x`.
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

end Real
