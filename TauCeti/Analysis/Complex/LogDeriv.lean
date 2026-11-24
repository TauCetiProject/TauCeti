/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Coordinate formulas for logarithmic derivatives

The derivative of a logarithm with a scaled argument is the reciprocal of the point on its
slit domain. Imaginary parts of inverse squares give the Cartesian entries of its Hessian.
-/

public section

namespace Complex

/-- The derivative of the logarithm of `z / c` is `z⁻¹` on the resulting slit domain. -/
theorem hasDerivAt_log_div_const (z : ℂ) {c : ℂ} (hz : z / c ∈ slitPlane) :
    HasDerivAt (fun w : ℂ ↦ log (w / c)) z⁻¹ z := by
  obtain ⟨hz0, hc⟩ := div_ne_zero_iff.mp (slitPlane_ne_zero hz)
  have h : HasDerivAt (fun w : ℂ ↦ w / c) (1 / c) z :=
    (hasDerivAt_id z).div_const c
  convert h.clog hz using 1
  field_simp [hc, hz0]

/-- The negative imaginary part of the inverse square in Cartesian coordinates. -/
theorem neg_im_one_div_sq (z : ℂ) :
    -((1 : ℂ) / z ^ 2).im = 2 * z.re * z.im / Complex.normSq z ^ 2 := by
  simp [pow_two, Complex.mul_im]
  ring

/-- The negative imaginary part of `I` divided by a square in Cartesian coordinates. -/
theorem neg_im_I_div_sq (z : ℂ) :
    -(Complex.I / z ^ 2).im = (z.im ^ 2 - z.re ^ 2) / Complex.normSq z ^ 2 := by
  simp [Complex.div_im, pow_two, Complex.normSq_mul, Complex.mul_re]
  ring

/-- The negative imaginary part of `-1` divided by a square in Cartesian coordinates. -/
theorem neg_im_neg_one_div_sq (z : ℂ) :
    -((-1 : ℂ) / z ^ 2).im = -(2 * z.re * z.im) / Complex.normSq z ^ 2 := by
  simpa only [neg_div, Complex.neg_im, neg_neg] using
    congrArg Neg.neg (neg_im_one_div_sq z)

end Complex
