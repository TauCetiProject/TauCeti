/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The complex partial of the real and imaginary parts of a holomorphic function

For `u : ℂ → ℝ`, the *complex partial* `∂ₓu - i ∂ᵧu`, written
`fderiv ℝ u z 1 - I * fderiv ℝ u z I`, is the function that Mathlib shows to be holomorphic for
harmonic `u` (`HarmonicAt.differentiableAt_complex_partial`). For a function `F` with complex
derivative `F'` at `z`, this file computes it for the real and imaginary parts of `F`:

* `u = Re F` has complex partial `F'` (`HasDerivAt.fderiv_re_one_sub_I_mul_fderiv_re_I`);
* `u = Im F` has complex partial `-i F'`, that is, `F' = i (∂ₓu - i ∂ᵧu)`
  (`HasDerivAt.I_mul_fderiv_im_one_sub_I_mul_fderiv_im_I`).

The second is the normalization of the Herglotz representation of a positive harmonic function on
the upper half-plane, where `u` is the imaginary part of a holomorphic `F`.

## Main results

* `HasDerivAt.fderiv_re_apply`, `HasDerivAt.fderiv_im_apply`: the real derivatives of `Re F` and
  `Im F` at `z` send `v` to `Re (F' v)` and `Im (F' v)`.
* `HasDerivAt.fderiv_re_one_sub_I_mul_fderiv_re_I`: `∂ₓ(Re F) - i ∂ᵧ(Re F) = F'`.
* `HasDerivAt.I_mul_fderiv_im_one_sub_I_mul_fderiv_im_I`: `i (∂ₓ(Im F) - i ∂ᵧ(Im F)) = F'`.
-/

public section

open Complex

namespace HasDerivAt

variable {F : ℂ → ℂ} {F' z : ℂ}

/-- The real derivative of the real part of a function with complex derivative `F'` sends `v` to
`Re (F' v)`. -/
theorem fderiv_re_apply (h : HasDerivAt F F' z) (v : ℂ) :
    fderiv ℝ (fun w => (F w).re) z v = (F' * v).re := by
  have hd := reCLM.hasFDerivAt.comp z (h.hasFDerivAt.restrictScalars ℝ)
  simp only [Function.comp_def, reCLM_apply] at hd
  simp [hd.fderiv, mul_comm]

/-- The real derivative of the imaginary part of a function with complex derivative `F'` sends
`v` to `Im (F' v)`. -/
theorem fderiv_im_apply (h : HasDerivAt F F' z) (v : ℂ) :
    fderiv ℝ (fun w => (F w).im) z v = (F' * v).im := by
  have hd := imCLM.hasFDerivAt.comp z (h.hasFDerivAt.restrictScalars ℝ)
  simp only [Function.comp_def, imCLM_apply] at hd
  simp [hd.fderiv, mul_comm]

/-- **The complex partial of a real part.** If `F` has complex derivative `F'` at `z`, the complex
partial `∂ₓu - i ∂ᵧu` of `u = Re F` at `z` is `F'`. -/
theorem fderiv_re_one_sub_I_mul_fderiv_re_I (h : HasDerivAt F F' z) :
    (fderiv ℝ (fun w => (F w).re) z 1 : ℂ) - I * fderiv ℝ (fun w => (F w).re) z I = F' := by
  rw [h.fderiv_re_apply, h.fderiv_re_apply]
  apply Complex.ext <;> simp

/-- **The complex partial of an imaginary part.** If `F` has complex derivative `F'` at `z`, the
complex partial `∂ₓu - i ∂ᵧu` of `u = Im F` at `z` satisfies `F' = i (∂ₓu - i ∂ᵧu)`. -/
theorem I_mul_fderiv_im_one_sub_I_mul_fderiv_im_I (h : HasDerivAt F F' z) :
    I * ((fderiv ℝ (fun w => (F w).im) z 1 : ℂ) - I * fderiv ℝ (fun w => (F w).im) z I) = F' := by
  rw [h.fderiv_im_apply, h.fderiv_im_apply]
  apply Complex.ext <;> simp

end HasDerivAt
