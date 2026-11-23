/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Multiplication by an exponential weight

Weighted Sobolev estimates replace a map `f` by `e^{φ} f` for a real weight function `φ`. The
derivative of the weighted map is `e^{φ}` times the derivative of `f` corrected by `dφ ⊗ f`, and
the square of the norm picks up the factor `e^{2φ}`.

## Main results

* `TauCeti.hasFDerivAt_exp_smul`: `w ↦ e^{φ(w)} • f w` has derivative
  `e^{φ(x)} • (f' + φ' ⊗ f x)` at `x`.
* `TauCeti.fderiv_exp_smul_apply`: the derivative of `w ↦ e^{φ(w)} • f w` in a direction `e` is
  `e^{φ(x)} • (Df(x) e + φ'(e) • f x)`.
* `TauCeti.norm_exp_smul_sq`: `‖e^x • v‖² = e^{2x} ‖v‖²`.
-/

public section

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The derivative of the weighted map `e^{φ} f` is `e^{φ} (Df + Dφ ⊗ f)`. -/
theorem hasFDerivAt_exp_smul {φ : E → ℝ} {φ' : E →L[ℝ] ℝ} {f : E → F} {f' : E →L[ℝ] F} {x : E}
    (hφ : HasFDerivAt φ φ' x) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun w ↦ Real.exp (φ w) • f w) (Real.exp (φ x) • (f' + φ'.smulRight (f x))) x := by
  refine (hφ.exp.smul hf).congr_fderiv ?_
  ext e
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  module

/-- The derivative of the weighted map `e^{φ} f` in a direction `e`. -/
theorem fderiv_exp_smul_apply {φ : E → ℝ} {φ' : E →L[ℝ] ℝ} {f : E → F} {x : E}
    (hφ : HasFDerivAt φ φ' x) (hf : DifferentiableAt ℝ f x) (e : E) :
    fderiv ℝ (fun w ↦ Real.exp (φ w) • f w) x e =
      Real.exp (φ x) • (fderiv ℝ f x e + φ' e • f x) := by
  simp [(hasFDerivAt_exp_smul hφ hf.hasFDerivAt).fderiv]

/-- `‖e^x v‖² = e^{2x} ‖v‖²`. -/
theorem norm_exp_smul_sq (x : ℝ) (v : F) :
    ‖Real.exp x • v‖ ^ 2 = Real.exp (2 * x) * ‖v‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, sq, ← Real.exp_add,
    two_mul]

end TauCeti
