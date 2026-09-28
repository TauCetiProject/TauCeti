/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: the Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The supporting line of `x ↦ x * log x`

The function `x ↦ x * log x` of Mathlib's `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` is
strictly convex on the nonnegative reals. This file records the two estimates about it that the
optimisation arguments over matrices and over measures use: the tangent line at a positive point
lies below the graph at every nonnegative point, and the loss of the function at a point that gives
up a small amount of its value is bounded by that same tangent line.

## Main results

* `Real.mul_log_sub_mul_log_ge`: for `0 < a` and `0 ≤ u`,
  `u * log u - a * log a ≥ (u - a) * (log a + 1)`.
* `Real.sub_mul_log_le`: for `0 ≤ t` and `t ≤ x / 2`,
  `(x - t) * log (x - t) - x * log x ≤ -t * (log x - log 2 + 1)`.

The first estimate is the tangent line at `a`, whose slope `log a + 1` is the derivative
`Real.deriv_mul_log` of the function. It is stated for `u = 0` as well, where the convention
`0 * log 0 = 0` of Mathlib makes its left side `-a * log a`, so that it applies at the boundary of
the domain without a case split.

The second estimate is the loss of the function at a value `x` that gives up an amount `t`: the
tangent line at `x - t` bounds the loss by `-t * (log (x - t) + 1)`, and the hypothesis
`t ≤ x / 2`, which bounds `log (x - t)` from below by `log x - log 2`, is where the constant
`log 2` of the statement comes from. It is stated for `t = 0`, and for the `x = 0` that the
hypotheses then force, so that a caller whose amount `t` may vanish needs no separate case.
-/
public section

namespace Real

/-- The supporting line of the convex function `u ↦ u * log u` at a positive point `a` lies below
the graph at every nonnegative `u`: with the slope `log a + 1` of `Real.deriv_mul_log`,
`u * log u - a * log a ≥ (u - a) * (log a + 1)`. -/
theorem mul_log_sub_mul_log_ge (a u : ℝ) (ha : 0 < a) (hu : 0 ≤ u) :
    u * Real.log u - a * Real.log a ≥ (u - a) * (Real.log a + 1) := by
  rcases lt_or_eq_of_le hu with hu' | hu0
  · have key : u * Real.log u - a * Real.log a - (u - a) * (Real.log a + 1)
        = a * ((u / a) * Real.log (u / a) - (u / a - 1)) := by
      rw [Real.log_div (x := u) (y := a) hu'.ne' ha.ne']
      field_simp
      ring
    have h1 : 0 ≤ (u / a) * Real.log (u / a) - (u / a - 1) :=
      sub_nonneg.mpr (Real.self_sub_one_le_mul_log (le_of_lt (div_pos hu' ha)))
    have h2 := mul_nonneg (le_of_lt ha) h1
    linarith
  · subst hu0
    simp only [Real.log_zero, zero_mul]
    linarith

/-- The loss of the function `u ↦ u * log u` at a value `x` that gives up an amount `t`, where
`0 ≤ t` and `t ≤ x / 2`, is at most `-t * (log x - log 2 + 1)`: the supporting line
`Real.mul_log_sub_mul_log_ge` at `x - t` bounds the loss by `-t * (log (x - t) + 1)`, and
`x - t ≥ x / 2` bounds `log (x - t)` from below by `log x - log 2`.

The case `x = 0`, which the hypotheses force together with `t = 0` and which makes both sides
zero, is included. -/
theorem sub_mul_log_le {x t : ℝ} (ht0 : 0 ≤ t) (htx : t ≤ x / 2) :
    (x - t) * Real.log (x - t) - x * Real.log x ≤ -t * (Real.log x - Real.log 2 + 1) := by
  have hx0' : 0 ≤ x := by nlinarith
  rcases lt_or_eq_of_le hx0' with hx0 | hx0
  · have hxt0 : 0 < x - t := by linarith
    have h1 : x * Real.log x - (x - t) * Real.log (x - t) ≥ t * (Real.log (x - t) + 1) := by
      have hle := mul_log_sub_mul_log_ge (x - t) x hxt0 hx0'
      linarith
    have hhalf : x / 2 ≤ x - t := by
      calc x / 2 = x - x / 2 := by ring
        _ ≤ x - t := sub_le_sub_left htx x
    have h2 : Real.log x - Real.log 2 ≤ Real.log (x - t) := by
      rw [← Real.log_div (x := x) (y := 2) (ne_of_gt hx0) (by norm_num : (2 : ℝ) ≠ 0)]
      exact Real.strictMonoOn_log.monotoneOn (a := x / 2) (b := x - t)
        (div_pos hx0 (by norm_num : (0 : ℝ) < 2)) hxt0 hhalf
    have h3 := mul_le_mul_of_nonneg_left h2 ht0
    linarith
  · have ht : t = 0 := by linarith
    subst ht
    simp

end Real
