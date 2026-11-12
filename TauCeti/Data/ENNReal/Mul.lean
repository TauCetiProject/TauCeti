/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ENNReal.Operations

/-!
# Bounds by triple products in `ℝ≥0∞`

A bound `L ≤ c * a * b` in `ℝ≥0∞` holds trivially when one factor is infinite and none vanishes.
So when `L` vanishes whenever a factor does, it suffices to prove the bound for finite `a` and `b`.
This is the shape of estimates such as `‖B(f, g)‖ ≤ C ‖B‖ ‖f‖ ‖g‖` with extended norms.

## Main declarations

* `ENNReal.le_mul_mul_of_ne_top`: the reduction of `L ≤ c * a * b` to finite `a` and `b`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- To bound `L` by `c * a * b`, it suffices to treat finite `a` and `b`, provided `L` vanishes
when `c`, `a` or `b` does: otherwise the right side is infinite. -/
theorem le_mul_mul_of_ne_top {L c a b : ℝ≥0∞} (hc : c = 0 → L = 0) (ha : a = 0 → L = 0)
    (hb : b = 0 → L = 0) (hfin : a ≠ ∞ → b ≠ ∞ → L ≤ c * a * b) : L ≤ c * a * b := by
  by_cases hc0 : c = 0
  · exact (hc hc0).le.trans zero_le
  by_cases ha0 : a = 0
  · exact (ha ha0).le.trans zero_le
  by_cases hb0 : b = 0
  · exact (hb hb0).le.trans zero_le
  by_cases hat : a = ∞
  · rw [hat, mul_top hc0, top_mul hb0]
    exact le_top
  by_cases hbt : b = ∞
  · rw [hbt, mul_top (mul_ne_zero hc0 ha0)]
    exact le_top
  exact hfin hat hbt

end ENNReal
