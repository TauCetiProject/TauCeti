/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Angle

/-!
# The angle between `a` and `a * w`

For a nonzero complex number `a`, the unoriented angle between `a` and `a * w` is
`arccos (Re w / |w|)` (`Complex.angle_self_mul_right`); for `w` in the open upper half-plane this
is the argument of `w`.

## Main results

* `Complex.angle_self_mul_right`: `angle a (a * w) = arccos (w.re / ‖w‖)` for `a ≠ 0`.
-/

public section

namespace Complex

/-- For `a ≠ 0`, the angle between `a` and `a * w` is `arccos (Re w / |w|)`; for `w` in the upper
half-plane this is the argument of `w`. -/
theorem angle_self_mul_right {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    InnerProductGeometry.angle a (a * w) = Real.arccos (w.re / ‖w‖) := by
  simpa [InnerProductGeometry.angle] using angle_mul_left ha 1 w

end Complex
