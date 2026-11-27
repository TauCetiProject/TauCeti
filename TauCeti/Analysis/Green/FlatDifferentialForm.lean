/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Basic
public import TauCeti.Analysis.Green.Basic
public import TauCeti.Analysis.InnerProductSpace.TwoDim

/-!
# Exterior derivative of planar circulation forms

The curl of the coefficients is the scalar of the exterior derivative in the positive area form
of the complex plane.
-/

public section

open Complex

namespace TauCeti.Green

attribute [local instance] Complex.finrank_real_complex_fact

/-- The flat exterior derivative of a differentiable planar one-form is its curl times the
positive area form. -/
theorem _root_.DifferentiableAt.extDeriv_oneForm_eq_smul_volumeFormL {P Q : ℂ → ℝ} {z : ℂ}
    (hω : DifferentiableAt ℝ (fun w ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1)
      (oneForm P Q w)) z) :
    extDeriv (fun w ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1)
      (oneForm P Q w)) z = curl P Q z • Complex.orientation.volumeFormL := by
  have hcurl : extDeriv (fun w ↦ ContinuousAlternatingMap.ofSubsingleton ℝ ℂ ℝ (0 : Fin 1)
      (oneForm P Q w)) z ![1, I] = curl P Q z := by
    simpa [curl] using extDeriv_apply_pair_of_differentiableAt hω (1 : ℂ) I
  ext v
  rw [ContinuousAlternatingMap.apply_eq_apply_one_I_mul_im, hcurl,
    ContinuousAlternatingMap.smul_apply, Complex.orientation_volumeFormL_apply, smul_eq_mul]

end TauCeti.Green
