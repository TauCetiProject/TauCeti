/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Bounds on a scaled logarithm as bounds by an exponential

For `x > 0` and `c > 0`, an upper bound `R` on `log x / c` or on `-log x / c` is the same as a
bound on `x` by `exp (c * R)` or `exp (-(c * R))`. Logarithmic coordinates `-log x / (2π)`, such
as the longitudinal coordinates of the cylindrical ends of the thrice-punctured sphere, turn
bounds on the coordinate into bounds on a norm in this way.

## Main results

* `Real.log_div_le_iff`: `log x / c ≤ R ↔ x ≤ exp (c * R)`.
* `Real.neg_log_div_le_iff`: `-log x / c ≤ R ↔ exp (-(c * R)) ≤ x`.
-/

public section

namespace Real

variable {x c R : ℝ}

/-- For `x > 0` and `c > 0`, the bound `log x / c ≤ R` says `x ≤ exp (c * R)`. -/
theorem log_div_le_iff (hx : 0 < x) (hc : 0 < c) : log x / c ≤ R ↔ x ≤ exp (c * R) := by
  rw [div_le_iff₀ hc, ← log_le_iff_le_exp hx, mul_comm R]

/-- For `x > 0` and `c > 0`, the bound `-log x / c ≤ R` says `exp (-(c * R)) ≤ x`. -/
theorem neg_log_div_le_iff (hx : 0 < x) (hc : 0 < c) :
    -log x / c ≤ R ↔ exp (-(c * R)) ≤ x := by
  rw [div_le_iff₀ hc, ← le_log_iff_exp_le hx, mul_comm R]
  constructor <;> intro h <;> linarith

end Real
