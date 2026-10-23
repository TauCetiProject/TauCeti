/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# When `a eᵗ` lies below one

For `a > 0`, the product `a eᵗ` is below one exactly when `t < -log a`. This is the domain
condition for power series in `a eᵗ` with radius of convergence one, such as moment-generating
functions obtained from probability-generating functions.

## Main results

* `Real.mul_exp_lt_one_iff`: `a * exp t < 1 ↔ t < -log a` for `0 < a`.
-/

public section

namespace Real

/-- For `a > 0`, the product `a * exp t` is below one exactly when `t < -log a`. -/
theorem mul_exp_lt_one_iff {a t : ℝ} (ha : 0 < a) : a * exp t < 1 ↔ t < -log a := by
  rw [← log_inv, lt_log_iff_exp_lt (inv_pos.mpr ha), ← one_div, lt_div_iff₀' ha]

end Real
