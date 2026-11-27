/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.SpecialFunctions.Exp
import TauCeti.Analysis.SpecialFunctions.Log.MulLog

/-!
# Bounds for the positive part of the logarithm

On `[0, ∞)` the positive part of the logarithm lies below the line `x ↦ exp (-1) * x`, which is
tangent to `log` at `x = e`. Integrated against a probability measure, this linear bound is what
controls the mean of `log⁺` by `log⁺` of the mean up to the additive constant `exp (-1)`.

The positive part of the logarithm is `1`-Lipschitz on all of `ℝ`: it is `log (max 1 |x|)`, and
`log` is `1`-Lipschitz on `[1, ∞)` (`Real.abs_log_sub_log_le`).

Off the unit circle, `-log ‖1 - w‖` for complex `w` is at most the logarithmic singularity
`log⁺ (1 / |1 - ‖w‖|)` of the modulus. Summed over the zeros of a product, this is the
singularity that a choice of good radius has to control.

## Main results

* `Real.posLog_le_exp_neg_one_mul`: `log⁺ x ≤ exp (-1) * x` for `0 ≤ x`.
* `Real.lipschitzWith_posLog`: `|log⁺ x - log⁺ y| ≤ |x - y|`.
* `Real.posLog_div_eq_log_of_abs_le_abs`, `Real.posLog_div_eq_zero_of_abs_le_abs`: the two values
  of `log⁺ (x / a)`, namely `log (x / a)` when `|a| ≤ |x|` and `0` when `|x| ≤ |a|`.
* `Complex.neg_log_norm_one_sub_le_posLog_one_div_abs_one_sub_norm`:
  `-log ‖1 - w‖ ≤ log⁺ (1 / |1 - ‖w‖|)` for `‖w‖ ≠ 1`.
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
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [NNReal.coe_one, one_mul, dist_eq, dist_eq, ← posLog_abs x, ← posLog_abs y,
    posLog_eq_log_max_one (abs_nonneg x), posLog_eq_log_max_one (abs_nonneg y)]
  have hmax : |max 1 (|x|) - max 1 (|y|)| ≤ |x - y| := by
    rw [max_comm 1 |x|, max_comm 1 |y|]
    exact (abs_max_sub_max_le_abs _ _ _).trans (abs_abs_sub_abs_le _ _)
  exact (abs_log_sub_log_le (le_max_left _ _) (le_max_left _ _)).trans hmax

/-- `log⁺ (x / a) = log (x / a)` when `|a| ≤ |x|`: then `1 ≤ |x / a|`, or `a = 0` and both sides
take the junk value `log 0 = 0`. -/
theorem posLog_div_eq_log_of_abs_le_abs {a x : ℝ} (h : |a| ≤ |x|) :
    log⁺ (x / a) = log (x / a) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rw [posLog_eq_log]
  rw [abs_div, one_le_div (abs_pos.2 ha)]
  exact h

/-- `log⁺ (x / a) = 0` when `|x| ≤ |a|`: then `|x / a| ≤ 1`, including `a = 0`, where the quotient
takes the junk value `0`. -/
theorem posLog_div_eq_zero_of_abs_le_abs {a x : ℝ} (h : |x| ≤ |a|) : log⁺ (x / a) = 0 := by
  rw [posLog_eq_zero_iff, abs_div]
  exact div_le_one_of_le₀ h (abs_nonneg a)

end Real

namespace Complex

/-- Off the unit circle, `-log ‖1 - w‖` is at most the logarithmic singularity
`log⁺ (1 / |1 - ‖w‖|)` of the modulus. The hypothesis is needed: for `w = exp (θ * I)` with
small `θ ≠ 0` the right side is the junk value `log⁺ (1 / 0) = 0`, while `‖1 - w‖ < 1`. -/
theorem neg_log_norm_one_sub_le_posLog_one_div_abs_one_sub_norm {w : ℂ} (hw : ‖w‖ ≠ 1) :
    -Real.log ‖1 - w‖ ≤ Real.posLog (1 / |1 - ‖w‖|) := by
  have h0 : 0 < |1 - ‖w‖| := abs_pos.mpr (sub_ne_zero.mpr hw.symm)
  have hle : |1 - ‖w‖| ≤ ‖1 - w‖ := by simpa using abs_norm_sub_norm_le (1 : ℂ) w
  calc
    -Real.log ‖1 - w‖ ≤ -Real.log |1 - ‖w‖| := neg_le_neg (Real.log_le_log h0 hle)
    _ = Real.log (1 / |1 - ‖w‖|) := by rw [one_div, Real.log_inv]
    _ ≤ Real.posLog (1 / |1 - ‖w‖|) := le_max_right _ _

end Complex
