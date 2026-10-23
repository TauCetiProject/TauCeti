/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Angle

/-!
# The angle between `I` and `I * w`

The unoriented angle between `I` and `I * w` is `arccos (Re w / |w|)` (`Complex.angle_I_I_mul`);
for `w` in the open upper half-plane this is the argument of `w`.

## Main results

* `Complex.angle_I_I_mul`: `angle I (I * w) = arccos (w.re / ‖w‖)`.
-/

public section

namespace Complex

/-- The angle between `I` and `I * w` is `arccos (Re w / |w|)`; for `w` in the upper half-plane
this is the argument of `w`. -/
theorem angle_I_I_mul (w : ℂ) :
    InnerProductGeometry.angle I (I * w) = Real.arccos (w.re / ‖w‖) := by
  rw [InnerProductGeometry.angle, Complex.inner, norm_mul, norm_I, one_mul, one_mul]
  simp [conj_I]

end Complex
