/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The derivative of a diagonal quadratic form

Over a nontrivially normed field `𝕜` and for a finite index type `ι`, the diagonal quadratic
function `x ↦ ∑ᵢ aᵢ xᵢ² / 2` on `ι → 𝕜` is named `TauCeti.diagonalQuadratic`. Over `ℝ` and up to an
additive constant, this is the normal form of a function at a nondegenerate critical point given by
the Morse lemma. When `2 ≠ 0` in `𝕜`, its derivative at `x` is `v ↦ ∑ᵢ aᵢ xᵢ vᵢ`, so its partial
derivatives are `aᵢ xᵢ`; over `ℝ` its second derivative is the diagonal bilinear form
`(v, w) ↦ ∑ᵢ aᵢ vᵢ wᵢ`. Its nondegenerate critical points and Morse index are computed in
`TauCeti.Analysis.Calculus.Morse.Pi`.

## Main definitions

* `TauCeti.diagonalQuadratic`: the diagonal quadratic function `∑ᵢ aᵢ xᵢ² / 2`.

## Main results

* `TauCeti.hasFDerivAt_diagonalQuadratic`: the derivative of `∑ᵢ aᵢ xᵢ² / 2` is
  `v ↦ ∑ᵢ aᵢ xᵢ vᵢ`.
* `TauCeti.fderiv_diagonalQuadratic_apply_single`: the partial derivatives of
  `∑ᵢ aᵢ xᵢ² / 2` are `aᵢ xᵢ`.
* `TauCeti.fderiv_fderiv_diagonalQuadratic_apply`: its second derivative is diagonal.
-/

public section

namespace TauCeti

section DiagonalQuadratic

open Function

section Field

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]

/-- The **diagonal quadratic function** `∑ᵢ aᵢ xᵢ² / 2` on `𝕜^ι`, whose Hessian is diagonal with
eigenvalues `aᵢ`. -/
noncomputable def diagonalQuadratic (a : ι → 𝕜) (x : ι → 𝕜) : 𝕜 :=
  ∑ i, a i * x i ^ 2 / 2

theorem diagonalQuadratic_apply (a x : ι → 𝕜) :
    diagonalQuadratic a x = ∑ i, a i * x i ^ 2 / 2 :=
  (rfl)

theorem contDiff_diagonalQuadratic (a : ι → 𝕜) {n : WithTop ℕ∞} :
    ContDiff 𝕜 n (diagonalQuadratic a) := by
  unfold diagonalQuadratic
  fun_prop

/-- The diagonal quadratic function `∑ᵢ aᵢ xᵢ² / 2` has derivative `v ↦ ∑ᵢ aᵢ xᵢ vᵢ` at `x`. -/
theorem hasFDerivAt_diagonalQuadratic [NeZero (2 : 𝕜)] (a x : ι → 𝕜) :
    HasFDerivAt (diagonalQuadratic a)
      (∑ i, (a i * x i) • ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι ↦ 𝕜) i) x := by
  have hs : HasFDerivAt (fun v : ι → 𝕜 ↦ ∑ i, a i * v i ^ 2) _ x := .fun_sum fun i _ ↦
    ((hasFDerivAt_pow 2).comp x (hasFDerivAt_apply (𝕜 := 𝕜) i x)).const_mul (a i)
  have he : diagonalQuadratic a = fun v ↦ (2 : 𝕜)⁻¹ * ∑ i, a i * v i ^ 2 := by
    funext v
    simp only [diagonalQuadratic_apply, Finset.mul_sum, div_eq_inv_mul]
  rw [he]
  convert hs.const_mul (2 : 𝕜)⁻¹ using 1
  ext v
  simp [Finset.mul_sum, mul_left_comm (2 : 𝕜)⁻¹, mul_assoc, two_ne_zero]

end Field

variable {ι : Type*} [Fintype ι]

/-- The summands of a diagonal quadratic function, as functions of one variable, have derivative
`c y`. -/
theorem deriv_mul_sq_div_two (c y : ℝ) : deriv (fun y : ℝ ↦ c * y ^ 2 / 2) y = c * y := by
  have h := ((hasDerivAt_pow 2 y).const_mul c).div_const 2
  rw [h.deriv]
  ring

private theorem deriv_deriv_mul_sq_div_two (c y : ℝ) :
    deriv (deriv fun y : ℝ ↦ c * y ^ 2 / 2) y = c := by
  rw [funext (deriv_mul_sq_div_two c)]
  simp

/-- The partial derivatives of `∑ᵢ aᵢ xᵢ² / 2` are `aᵢ xᵢ`. -/
@[simp]
theorem fderiv_diagonalQuadratic_apply_single [DecidableEq ι] (a x : ι → ℝ) (i : ι) :
    fderiv ℝ (diagonalQuadratic a) x (Pi.single i 1) = a i * x i := by
  simp [(hasFDerivAt_diagonalQuadratic a x).fderiv, Pi.single_apply]

/-- The Hessian of `∑ᵢ aᵢ xᵢ² / 2` is the diagonal form `∑ᵢ aᵢ vᵢ wᵢ`. -/
@[simp]
theorem fderiv_fderiv_diagonalQuadratic_apply (a x v w : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (diagonalQuadratic a)) x v w = ∑ i, a i * v i * w i := by
  unfold diagonalQuadratic
  rw [fderiv_fderiv_sum_comp_eval_apply (φ := fun i y ↦ a i * y ^ 2 / 2) fun i ↦ by fun_prop]
  simp [deriv_deriv_mul_sq_div_two]

end DiagonalQuadratic

end TauCeti
