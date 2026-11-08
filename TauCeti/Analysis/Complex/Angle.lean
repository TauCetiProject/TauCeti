/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Angle

/-!
# The angle between `a` and `a * w`, and a rotation identity

For a nonzero complex number `a`, the unoriented angle between `a` and `a * w` is
`arccos (Re w / |w|)` (`Complex.angle_self_mul_right`); for `w` in the open upper half-plane this
is the argument of `w`. The file also records a rotation identity for `exp (θ I)`
(`Complex.im_exp_neg_mul_mul_ofReal_mul_exp`).

## Main results

* `Complex.angle_self_mul_right`: `angle a (a * w) = arccos (w.re / ‖w‖)` for `a ≠ 0`.
* `Complex.im_exp_neg_mul_mul_ofReal_mul_exp`: `(exp (-θ I) * (r * exp (θ I))).im = 0`.
-/

public section

namespace Complex

/-- For `a ≠ 0`, the angle between `a` and `a * w` is `arccos (Re w / |w|)`; for `w` in the upper
half-plane this is the argument of `w`. -/
theorem angle_self_mul_right {a : ℂ} (ha : a ≠ 0) (w : ℂ) :
    InnerProductGeometry.angle a (a * w) = Real.arccos (w.re / ‖w‖) := by
  simpa [InnerProductGeometry.angle] using angle_mul_left ha 1 w

/-- Rotating a real multiple of `exp (θ I)` by `exp (-θ I)` gives a real number. -/
theorem im_exp_neg_mul_mul_ofReal_mul_exp (θ r : ℝ) :
    (Complex.exp (-θ * Complex.I) * ((r : ℂ) * Complex.exp (θ * Complex.I))).im = 0 := by
  rw [mul_left_comm, ← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero, mul_one,
    Complex.ofReal_im]

end Complex
