/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The logit function inverts the sigmoid

Mathlib's `Real.sigmoid` maps `ℝ` increasingly onto `Set.Ioo 0 1`. Its inverse on that interval is
the logit `u ↦ log (u / (1 - u))`. This file records the facts about the pair that are used to
transport the uniform law on the unit interval along the logit: the logit is a right inverse of
the sigmoid, and the logit of a level lies below a point exactly when the level lies below the
sigmoid of that point. It also writes the derivative `σ (1 - σ)` of the sigmoid in terms of the
exponential.

## Main results

* `Real.sigmoid_log_div_one_sub` — `sigmoid (log (u / (1 - u))) = u` for `0 < u < 1`;
* `Real.log_div_one_sub_le_iff` — `log (u / (1 - u)) ≤ y ↔ u ≤ sigmoid y` for `0 < u < 1`;
* `Real.measurable_logit_affine` — affine transformations of the logit are measurable;
* `Real.sigmoid_mul_one_sub_sigmoid` — the derivative of the sigmoid is
  `sigmoid y * (1 - sigmoid y) = exp (-y) / (1 + exp (-y)) ^ 2`.
-/

public section

namespace Real

/-- The logit `u ↦ log (u / (1 - u))` is a right inverse of the sigmoid on the open unit
interval. -/
@[simp]
theorem sigmoid_log_div_one_sub {u : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    sigmoid (log (u / (1 - u))) = u := by
  have h1' : 0 < 1 - u := sub_pos.mpr h1
  rw [sigmoid_def, exp_neg, exp_log (div_pos h0 h1'), inv_div]
  field_simp
  ring

/-- The logit is a left inverse of the sigmoid. -/
@[simp]
theorem log_sigmoid_div_one_sub (x : ℝ) :
    log (sigmoid x / (1 - sigmoid x)) = x := by
  apply sigmoid_injective
  exact sigmoid_log_div_one_sub (sigmoid_pos x) (sigmoid_lt_one x)

/-- On the open unit interval, the logit of `u` lies below `y` exactly when `u` lies below the
sigmoid of `y`. -/
theorem log_div_one_sub_le_iff {u y : ℝ} (h0 : 0 < u) (h1 : u < 1) :
    log (u / (1 - u)) ≤ y ↔ u ≤ sigmoid y := by
  rw [← sigmoid_le_iff, sigmoid_log_div_one_sub h0 h1]

/-- An affine transformation of the logit is measurable. -/
@[fun_prop]
theorem measurable_logit_affine (m s : ℝ) :
    Measurable fun u : ℝ => m + s * log (u / (1 - u)) := by
  fun_prop

/-- The derivative `sigmoid y * (1 - sigmoid y)` of the sigmoid, written through the
exponential. -/
theorem sigmoid_mul_one_sub_sigmoid (y : ℝ) :
    sigmoid y * (1 - sigmoid y) = exp (-y) / (1 + exp (-y)) ^ 2 := by
  rw [← sigmoid_neg, ← sigmoid_mul_rexp_neg, sigmoid_def]
  field

end Real
