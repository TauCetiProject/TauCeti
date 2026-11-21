/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SquaredDistance
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.Morse.ScalarComposition

/-!
# The Hessian of the squared norm

The squared norm `z ↦ ‖z‖ ^ 2` on a real inner product space is the model of a nondegenerate
minimum. Its second derivative is the constant bilinear form `2 ⟪v, w⟫`
(`TauCeti.fderiv_fderiv_norm_sq_apply`), so its Hessian quadratic form is `v ↦ 2 * ‖v‖ ^ 2` at
every point and its Morse index vanishes everywhere. The hemisphere height `x ↦ √(a - ‖x‖²)`, a
scalar reparametrization of it, has Hessian `-‖v‖² / √a` at the origin.

These are the real inputs for the Levi form and the inertia of the squared norm of a complex inner
product space, the basic strictly plurisubharmonic function.

## Main results

* `TauCeti.hessianQuadraticForm_norm_sq`: its Hessian quadratic form is `2 * ‖v‖ ^ 2`.
* `TauCeti.morseIndex_norm_sq`: its Morse index vanishes at every point.
* `TauCeti.hessianQuadraticForm_sqrt_sub_norm_sq_zero`: the Hessian quadratic form of the
  hemisphere height `√(a - ‖x‖²)` at the origin is `-‖v‖² / √a`.
-/

public section

open RealInnerProductSpace

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

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

/-- The Hessian quadratic form of the hemisphere height `x ↦ √(a - ‖x‖²)` at the origin is
`v ↦ -‖v‖² / √a`. -/
theorem hessianQuadraticForm_sqrt_sub_norm_sq_zero {a : ℝ} (ha : 0 < a) (v : F) :
    hessianQuadraticForm (fun x : F ↦ √(a - ‖x‖ ^ 2)) 0 v = -(‖v‖ ^ 2 / √a) := by
  have hn : ContDiffAt ℝ 2 (fun y : F ↦ ‖y‖ ^ 2) 0 := (contDiff_norm_sq ℝ).contDiffAt
  have hc : fderiv ℝ (fun y : F ↦ ‖y‖ ^ 2) 0 = 0 := by
    simp
  have h0 : ‖(0 : F)‖ ^ 2 = 0 := by simp
  have ha' : a - 0 ≠ 0 := by simpa using ha.ne'
  have hd : HasDerivAt (fun t : ℝ ↦ √(a - t)) (-(1 / (2 * √a))) (‖(0 : F)‖ ^ 2) := by
    rw [h0]
    convert ((hasDerivAt_id' (0 : ℝ)).const_sub a).sqrt ha' using 1
    rw [sub_zero, neg_div]
  have hs : ContDiffAt ℝ 2 (fun t : ℝ ↦ √(a - t)) (‖(0 : F)‖ ^ 2) := by
    rw [h0]
    exact (Real.contDiffAt_sqrt ha').comp 0 (contDiffAt_const.sub contDiffAt_id)
  -- `√(a - ‖x‖²)` is `t ↦ √(a - t)` after the critical function `‖x‖²`; `change` unfolds the
  -- composition.
  change hessianQuadraticForm ((fun t : ℝ ↦ √(a - t)) ∘ fun y : F ↦ ‖y‖ ^ 2) 0 v = _
  rw [hessianQuadraticForm_scalar_comp (f := fun y ↦ ‖y‖ ^ 2) hs hn hc,
    smul_apply, hd.deriv, hessianQuadraticForm_norm_sq, smul_eq_mul]
  field_simp

end TauCeti
