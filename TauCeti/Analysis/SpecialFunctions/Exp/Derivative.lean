/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Derivatives of exponential functions

The derivative and the norm of the Fréchet derivative of an exponential with linear exponent
are given by `Real.deriv_exp_mul` and `Real.norm_fderiv_exp_mul`.
-/

public section

namespace Real

/-- The derivative of an exponential with linear exponent. -/
theorem deriv_exp_mul (a x : ℝ) :
    deriv (fun y : ℝ => exp (a * y)) x = a * exp (a * x) := by
  simpa [mul_comm] using (((hasDerivAt_id x).const_mul a).exp).deriv

/-- The norm of the Fréchet derivative of an exponential with linear exponent. -/
theorem norm_fderiv_exp_mul (a x : ℝ) :
    ‖fderiv ℝ (fun y : ℝ => exp (a * y)) x‖ = |a| * exp (a * x) := by
  rw [← norm_deriv_eq_norm_fderiv, deriv_exp_mul, Real.norm_eq_abs, abs_mul,
    abs_of_pos (exp_pos _)]

end Real
