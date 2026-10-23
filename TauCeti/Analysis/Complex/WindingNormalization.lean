/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Real part of the complex winding normalization

Multiplication by `(2πi)⁻¹` converts an imaginary part into the real normalized index.
-/

public section

namespace Complex

/-- The real part of a normalized complex winding integral is its imaginary part divided by
`2π`. -/
theorem re_inv_two_pi_I_mul (w : ℂ) :
    ((2 * (Real.pi : ℂ) * I)⁻¹ * w).re = w.im / (2 * Real.pi) := by
  have he : 2 * (Real.pi : ℂ) * I = ((2 * Real.pi : ℝ) : ℂ) * I := by norm_cast
  rw [he, mul_inv_rev, inv_I]
  simp [Complex.mul_re, Complex.mul_im, div_eq_mul_inv]
  ring

end Complex
