/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Positive divided differences of the real exponential

The divided difference of the exponential is the integral of the exponential along the segment
between its arguments. In particular it is strictly positive, including when the arguments
coincide. These are the scalar coefficients in the derivative of the matrix exponential at a
Hermitian matrix.
-/

public section

namespace Real

/-- The divided difference of the exponential is its average along a segment. -/
theorem dslope_exp_eq_integral (a b : ℝ) :
    dslope exp a b = ∫ t in (0 : ℝ)..1, exp ((1 - t) * a + t * b) := by
  have heq (t : ℝ) : (1 - t) * a + t * b = a + t * (b - a) := by ring
  simp_rw [heq]
  have h := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (by fun_prop : ContinuousOn (fun t : ℝ ↦ exp (a + t * (b - a))) (Set.Icc 0 1))
    (fun t _ ↦ hasDerivAt_exp (a + t * (b - a)))
  simp only [smul_eq_mul, add_sub_cancel] at h
  by_cases hab : b = a
  · simp [hab]
  · rw [dslope_of_ne exp hab, slope_def_field, div_eq_iff (sub_ne_zero.mpr hab)]
    simpa only [mul_comm] using h.symm

/-- All divided differences of the real exponential are strictly positive. -/
theorem dslope_exp_pos (a b : ℝ) : 0 < dslope exp a b := by
  rw [dslope_exp_eq_integral]
  exact intervalIntegral.integral_pos (by norm_num) (by fun_prop)
    (fun t _ ↦ (exp_pos _).le) ⟨0, by simp, exp_pos _⟩

end Real
