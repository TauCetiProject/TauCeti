/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Cancelling a real power in `ℝ≥0∞`

If `X ^ r ≤ C * X ^ (r - 1)` for a finite `X`, then `X ≤ C`: the factor `X ^ (r - 1)` cancels,
since it is neither `0` nor `∞` unless `X = 0`, in which case the conclusion is trivial. This is
the last step of every norming argument for `Lᵖ` norms, where `X` is a norm and `X ^ r` is its
pairing with the extremal function.

## Main declarations

* `ENNReal.le_of_rpow_le_mul_rpow_sub_one`: `X ^ r ≤ C * X ^ (r - 1)` gives `X ≤ C` for a finite
  `X`.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- If `X ^ r ≤ C * X ^ (r - 1)` for a finite `X`, then `X ≤ C`. -/
theorem le_of_rpow_le_mul_rpow_sub_one {X C : ℝ≥0∞} {r : ℝ} (hX : X ≠ ∞)
    (h : X ^ r ≤ C * X ^ (r - 1)) : X ≤ C := by
  rcases eq_or_ne X 0 with hX0 | hX0
  · simp [hX0]
  have hXr : X ^ r = X ^ (r - 1) * X := by
    conv_lhs => rw [show r = (r - 1) + 1 by ring]
    rw [rpow_add _ _ hX0 hX, rpow_one]
  have hpow0 : X ^ (r - 1) ≠ 0 := by simp [rpow_eq_zero_iff, hX0, hX]
  rw [hXr, mul_comm C] at h
  exact (ENNReal.mul_le_mul_iff_right hpow0 (rpow_ne_top_of_ne_zero hX0 hX)).1 h

end ENNReal
