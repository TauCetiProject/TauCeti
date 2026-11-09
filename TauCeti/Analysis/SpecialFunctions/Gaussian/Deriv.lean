/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.SquaredDistance

/-!
# Derivatives of the Gaussian on a real inner product space

This file computes the first and second Fréchet derivatives of the Gaussian
`x ↦ exp (-α ‖x - y‖²)` on a real inner product space.

## Main results

* `TauCeti.fderiv_exp_neg_mul_norm_sub_sq_apply`: the derivative in the direction `w` is
  `-2 α ⟪x - y, w⟫ exp (-α ‖x - y‖²)`.
* `TauCeti.fderiv_fderiv_exp_neg_mul_norm_sub_sq_apply`: the Hessian is
  `(4 α² ⟪x - y, w⟫ ⟪x - y, w'⟫ - 2 α ⟪w, w'⟫) exp (-α ‖x - y‖²)`.
-/

public section

noncomputable section

namespace TauCeti

open RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The derivative of the Gaussian `z ↦ exp (-α ‖z - y‖²)` at `x` in the direction `w` is
`-2 α ⟪x - y, w⟫ exp (-α ‖x - y‖²)`. -/
theorem fderiv_exp_neg_mul_norm_sub_sq_apply (α : ℝ) (y x w : E) :
    fderiv ℝ (fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2)) x w =
      -2 * α * ⟪x - y, w⟫ * Real.exp (-α * ‖x - y‖ ^ 2) := by
  have h : HasFDerivAt (fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2)) _ x :=
    (((hasFDerivAt_id x).sub_const y).norm_sq.const_mul (-α)).exp
  rw [h.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.id_apply, id_eq, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- **The Hessian of the Gaussian.** The second derivative of `z ↦ exp (-α ‖z - y‖²)` at `x` is
`(4 α² ⟪x - y, w⟫ ⟪x - y, w'⟫ - 2 α ⟪w, w'⟫) exp (-α ‖x - y‖²)`. -/
theorem fderiv_fderiv_exp_neg_mul_norm_sub_sq_apply (α : ℝ) (y x w w' : E) :
    fderiv ℝ (fderiv ℝ fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2)) x w w' =
      (4 * α ^ 2 * ⟪x - y, w⟫ * ⟪x - y, w'⟫ - 2 * α * ⟪w, w'⟫) * Real.exp (-α * ‖x - y‖ ^ 2) := by
  -- The Gaussian is `φ ∘ q` with `φ s = exp (-α s)` and `q z = ‖z - y‖²`.
  let q : E → ℝ := fun z ↦ ‖z - y‖ ^ 2
  let φ : ℝ → ℝ := fun s ↦ Real.exp (-α * s)
  have hcomp : (fun z ↦ Real.exp (-α * ‖z - y‖ ^ 2)) = φ ∘ q := rfl
  have hq : ContDiffAt ℝ 2 q x :=
    ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).contDiffAt
  have hφ : ContDiffAt ℝ 2 φ (q x) := by fun_prop
  have hD1 (w : E) : fderiv ℝ q x w = 2 * ⟪x - y, w⟫ := by
    have h := fderiv_norm_sq_sub_comp (i := id) (a := y) (x := x) differentiableAt_id
    simpa [q, inner_sub_left] using congrArg (· w) h
  have hid : fderiv ℝ (fderiv ℝ (id : E → E)) x = 0 := by
    have h : fderiv ℝ (id : E → E) = fun _ ↦ ContinuousLinearMap.id ℝ E :=
      funext fun _ ↦ fderiv_id
    rw [h]
    exact fderiv_const_apply _
  have hD2 (w w' : E) : fderiv ℝ (fderiv ℝ q) x w w' = 2 * ⟪w, w'⟫ := by
    have h := fderiv_fderiv_norm_sq_sub_comp_apply (i := id) (a := y) (x := x) contDiffAt_id w w'
    simpa [q, hid] using h
  have hφ1 : deriv φ = fun s ↦ -α * φ s := by
    have h := iteratedDeriv_exp_const_mul 1 (-α)
    rwa [iteratedDeriv_one, pow_one] at h
  have hφ2 : iteratedDeriv 2 φ = fun s ↦ α ^ 2 * φ s := by
    have h := iteratedDeriv_exp_const_mul 2 (-α)
    rwa [neg_sq] at h
  rw [hcomp, fderiv_fderiv_scalar_comp_apply hφ hq, hD1, hD1, hD2, hφ1, hφ2]
  simp only [smul_eq_mul, φ, q]
  ring

end TauCeti
