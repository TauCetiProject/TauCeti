/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import TauCeti.Analysis.Calculus.Morse.Index

/-!
# The Hessian of the squared norm

The squared norm `z ↦ ‖z‖ ^ 2` on a real inner product space is the model of a nondegenerate
minimum. Its second derivative is the constant bilinear form `2 ⟪v, w⟫`, so its Hessian quadratic
form is `v ↦ 2 * ‖v‖ ^ 2` at every point and its Morse index vanishes everywhere.

These are the real inputs for the Levi form and the inertia of the squared norm of a complex inner
product space, the basic strictly plurisubharmonic function.

## Main results

* `TauCeti.fderiv_fderiv_norm_sq_apply`: the second derivative of `‖·‖ ^ 2` is `2 ⟪v, w⟫`.
* `TauCeti.hessianQuadraticForm_norm_sq`: its Hessian quadratic form is `2 * ‖v‖ ^ 2`.
* `TauCeti.morseIndex_norm_sq`: its Morse index vanishes at every point.
-/

public section

open RealInnerProductSpace

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The second derivative of the squared norm is twice the inner product, at every point. -/
@[simp]
theorem fderiv_fderiv_norm_sq_apply (x v w : F) :
    fderiv ℝ (fderiv ℝ fun z : F ↦ ‖z‖ ^ 2) x v w = 2 * ⟪v, w⟫ := by
  rw [fderiv_norm_sq, fderiv_const_smul (innerSL ℝ).differentiableAt, ContinuousLinearMap.fderiv,
    smul_apply, smul_apply, innerSL_apply_apply, two_nsmul, two_mul]

/-- The Hessian quadratic form of the squared norm is `v ↦ 2 * ‖v‖ ^ 2`, at every point. -/
theorem hessianQuadraticForm_norm_sq (x v : F) :
    hessianQuadraticForm (fun z ↦ ‖z‖ ^ 2) x v = 2 * ‖v‖ ^ 2 := by
  rw [hessianQuadraticForm_apply, fderiv_fderiv_norm_sq_apply, real_inner_self_eq_norm_sq]

/-- The squared norm has Morse index zero at every point. -/
@[simp]
theorem morseIndex_norm_sq [FiniteDimensional ℝ F] (x : F) :
    morseIndex (fun z ↦ ‖z‖ ^ 2) x = 0 := by
  rw [morseIndex_def, ← QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero]
  intro v
  rw [hessianQuadraticForm_norm_sq]
  positivity

end TauCeti
