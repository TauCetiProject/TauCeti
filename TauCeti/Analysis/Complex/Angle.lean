/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Angle

/-!
# The angle between `I` and `I * w`

For `w` in the open upper half-plane, the unoriented angle between `I` and `I * w` is the
argument of `w`, written as `arccos (Re w / |w|)` (`Complex.angle_I_I_mul`).

## Main results

* `Complex.angle_I_I_mul`: `angle I (I * w) = arccos (w.re / ‖w‖)` for `0 < w.im`.
-/

public section

namespace Complex

/-- The angle between `I` and `I * w`, for `w` in the upper half-plane, is the argument of `w`. -/
theorem angle_I_I_mul {w : ℂ} (hw : 0 < w.im) :
    InnerProductGeometry.angle Complex.I (Complex.I * w) = Real.arccos (w.re / ‖w‖) := by
  have h := Complex.angle_mul_left Complex.I_ne_zero 1 w
  rw [mul_one] at h
  rw [h, Complex.angle_one_left (fun h0 ↦ by simp [h0] at hw), Complex.arg_of_im_pos hw,
    abs_of_nonneg (Real.arccos_nonneg _)]

end Complex
