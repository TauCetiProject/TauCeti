/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Angle
public import Mathlib.Analysis.Complex.Order

/-!
# The angle between `a` and `a * w`, and a rotation identity

For a nonzero complex number `a`, the unoriented angle between `a` and `a * w` is
`arccos (Re w / |w|)` (`Complex.angle_self_mul_right`); for `w` in the open upper half-plane this
is the argument of `w`. The file also records two rotation identities for `exp (-θ I)`: the
rotation of a real multiple of `exp (θ I)` (`Complex.im_exp_neg_mul_mul_ofReal_mul_exp`), and the
height of a horizontal step (`Complex.im_exp_neg_mul_sub_sub_eq_of_le`).

## Main results

* `Complex.angle_self_mul_right`: `angle a (a * w) = arccos (w.re / ‖w‖)` for `a ≠ 0`.
* `Complex.im_exp_neg_mul_mul_ofReal_mul_exp`: `(exp (-θ I) * (r * exp (θ I))).im = 0`.
* `Complex.im_exp_neg_mul_sub_sub_eq_of_le`: the height of a horizontal step `x ≤ y` rotated by
  `exp (-θ * I)` is its length times `sin (-θ)`.
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

open scoped ComplexOrder in
/-- **A horizontal step, rotated by `-θ`, has height `r * sin (-θ)`.**  If `x ≤ y` in the order on
`ℂ` (same imaginary part, real part not larger), then after multiplying by `exp (-θ * I)` the
difference of heights is the length `r = (y - x).re ≥ 0` times `sin (-θ)`. -/
lemma im_exp_neg_mul_sub_sub_eq_of_le (θ : ℝ) (w : ℂ) {x y : ℂ} (hxy : x ≤ y) :
    ∃ r, 0 ≤ r ∧ (Complex.exp (-θ * Complex.I) * (y - w)).im -
      (Complex.exp (-θ * Complex.I) * (x - w)).im = r * Real.sin (-θ) := by
  refine ⟨(y - x).re, sub_nonneg.mpr (Complex.le_def.mp hxy).1, ?_⟩
  have hu : (Complex.exp (-θ * Complex.I)).im = Real.sin (-θ) := by
    have h := Complex.exp_ofReal_mul_I_im (-θ)
    push_cast at h
    exact h
  rw [← Complex.sub_im, ← mul_sub, sub_sub_sub_cancel_right]
  simp only [Complex.mul_im, Complex.sub_im, (Complex.le_def.mp hxy).2, hu, sub_self, mul_zero,
    zero_add]
  ring

end Complex
