/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A lower bound for the logarithm of a ratio of differences

For `a < x` and `b < x`, the logarithm `log ((x - a) / (x - b))` is at least
`(b - a) / (x - a)`. This is `1 - y⁻¹ ≤ log y` at `y = (x - a) / (x - b)`. As `x → ∞` both sides
are asymptotic to `(b - a) / x`, which is what makes the bound useful for showing that
`x ↦ log ((x - a) / (x - b))` is not integrable at infinity.

## Main results

* `Real.sub_div_sub_le_log_div_sub`: `(b - a) / (x - a) ≤ log ((x - a) / (x - b))`.
-/

public section

namespace Real

/-- For `a < x` and `b < x`, the logarithm `log ((x - a) / (x - b))` is at least
`(b - a) / (x - a)`. -/
theorem sub_div_sub_le_log_div_sub {a b x : ℝ} (hax : a < x) (hbx : b < x) :
    (b - a) / (x - a) ≤ log ((x - a) / (x - b)) := by
  calc (b - a) / (x - a) = 1 - ((x - a) / (x - b))⁻¹ := by field_simp; ring
    _ ≤ _ := one_sub_inv_le_log_of_pos (div_pos (sub_pos.2 hax) (sub_pos.2 hbx))

end Real
