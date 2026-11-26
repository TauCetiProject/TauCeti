/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential

import Mathlib.Analysis.Complex.Basic

/-!
# The quotient `exp L / u` for small `L` and `u` near `1`

Mathlib's `Complex.norm_exp_sub_one_le` gives `‖exp L - 1‖ ≤ 2 ‖L‖` for `‖L‖ ≤ 1`. Comparing
`exp L` with a second number `u` near `1`, relative to `u`, gives
`‖exp L / u - 1‖ ≤ (2 ‖L‖ + ‖u - 1‖) / (1 - ‖u - 1‖)` for `‖u - 1‖ < 1`. This is the form in which
a root `exp L` of a product close to `1` is compared with one of the factors.

## Main results

* `Complex.norm_exp_div_sub_one_le`: for `‖L‖ ≤ 1` and `‖u - 1‖ < 1`,
  `‖exp L / u - 1‖ ≤ (2 ‖L‖ + ‖u - 1‖) / (1 - ‖u - 1‖)`.
-/

public section

namespace Complex

/-- **`exp L / u` is near `1` when `L` is small and `u` is near `1`.** For `‖L‖ ≤ 1` and
`‖u - 1‖ < 1`, `‖exp L / u - 1‖ ≤ (2 ‖L‖ + ‖u - 1‖) / (1 - ‖u - 1‖)`. The numerator bounds
`‖exp L - u‖` through `Complex.norm_exp_sub_one_le`, the denominator bounds `‖u‖` from below. -/
theorem norm_exp_div_sub_one_le {L u : ℂ} (hL : ‖L‖ ≤ 1) (hu : ‖u - 1‖ < 1) :
    ‖exp L / u - 1‖ ≤ (2 * ‖L‖ + ‖u - 1‖) / (1 - ‖u - 1‖) := by
  have hu' : 1 - ‖u - 1‖ ≤ ‖u‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - u)
    rw [norm_one, sub_sub_cancel, norm_sub_rev] at this
    linarith
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have h : ‖exp L - u‖ ≤ 2 * ‖L‖ + ‖u - 1‖ :=
    calc ‖exp L - u‖ = ‖(exp L - 1) - (u - 1)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖exp L - 1‖ + ‖u - 1‖ := norm_sub_le _ _
      _ ≤ 2 * ‖L‖ + ‖u - 1‖ := by grw [norm_exp_sub_one_le hL]
  rw [div_sub_one hu0, norm_div]
  exact div_le_div₀ (by positivity) h (by linarith) hu'

end Complex
