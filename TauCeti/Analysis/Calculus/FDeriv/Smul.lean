/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Directional derivative estimates for scalar multiplication

Multiplying a map by a real scalar function separates its derivative into a principal part and
an error involving the derivative of the scalar function. The estimate below bounds the sum of
the squared derivative norms in two arbitrary directions, as used in cutoff energy estimates.
It requires differentiability only at the point where the estimate is evaluated.

## Main result

* `TauCeti.cutoff_sq_mul_norm_fderiv_sq_le`: the two-direction cutoff derivative estimate.
-/

public section

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The squared derivative energy in two directions, weighted by a real scalar function, is
bounded by the energy of the scalar multiple and the scalar derivative error. No compact support
or normalization of the directions is needed. -/
theorem cutoff_sq_mul_norm_fderiv_sq_le {u : E → V} {χ : E → ℝ} {z : E}
    (hu : DifferentiableAt ℝ u z) (hχ : DifferentiableAt ℝ χ z) (e₁ e₂ : E) :
    χ z ^ 2 * (‖fderiv ℝ u z e₁‖ ^ 2 + ‖fderiv ℝ u z e₂‖ ^ 2) ≤
      2 * (‖fderiv ℝ (χ • u) z e₁‖ ^ 2 + ‖fderiv ℝ (χ • u) z e₂‖ ^ 2) +
      2 * (fderiv ℝ χ z e₁ ^ 2 + fderiv ℝ χ z e₂ ^ 2) * ‖u z‖ ^ 2 := by
  have hderiv (e : E) : fderiv ℝ (χ • u) z e =
      χ z • fderiv ℝ u z e + fderiv ℝ χ z e • u z := by
    simpa only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, add_comm] using
      congrArg (fun L : E →L[ℝ] V => L e) (fderiv_smul hχ hu)
  have hdir (e : E) :
      χ z ^ 2 * ‖fderiv ℝ u z e‖ ^ 2 ≤
        2 * ‖fderiv ℝ (χ • u) z e‖ ^ 2 + 2 * fderiv ℝ χ z e ^ 2 * ‖u z‖ ^ 2 := by
    have heq : χ z • fderiv ℝ u z e =
        fderiv ℝ (χ • u) z e - fderiv ℝ χ z e • u z := by rw [hderiv]; abel
    have hnorm := norm_sub_le (fderiv ℝ (χ • u) z e) (fderiv ℝ χ z e • u z)
    rw [← heq, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
    have hsq := mul_self_le_mul_self (by positivity) hnorm
    nlinarith only [hsq, sq_abs (χ z), sq_abs (fderiv ℝ χ z e),
      add_sq_le (a := ‖fderiv ℝ (χ • u) z e‖) (b := |fderiv ℝ χ z e| * ‖u z‖)]
  nlinarith only [hdir e₁, hdir e₂]

end TauCeti

end
