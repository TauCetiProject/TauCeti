/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The derivative of a diagonal quadratic form

The diagonal quadratic form `u ↦ c + (1/2) Σᵢ wᵢ uᵢ²` on `Fin n → ℝ` has derivative
`v ↦ Σᵢ wᵢ uᵢ vᵢ` at `u`. This is the normal form of a function at a nondegenerate critical point
given by the Morse lemma.

For a finite index type `ι`, the function `x ↦ ∑ᵢ aᵢ xᵢ² / 2` on `ι → ℝ` is named
`TauCeti.diagonalQuadratic`. Its partial derivatives are `aᵢ xᵢ` and its second derivative is the
diagonal bilinear form `(v, w) ↦ ∑ᵢ aᵢ vᵢ wᵢ`. Its nondegenerate critical points and Morse index are
computed in `TauCeti.Analysis.Calculus.Morse.Pi`.

## Main definitions

* `TauCeti.diagonalQuadratic`: the diagonal quadratic function `∑ᵢ aᵢ xᵢ² / 2`.

## Main results

* `TauCeti.hasFDerivAt_diagonalQuadratic`: the derivative of a diagonal quadratic form.
* `TauCeti.fderiv_diagonalQuadratic_apply_single`: the partial derivatives of
  `∑ᵢ aᵢ xᵢ² / 2` are `aᵢ xᵢ`.
* `TauCeti.fderiv_fderiv_diagonalQuadratic_apply`: its second derivative is diagonal.
-/

public section

namespace TauCeti

/-- The diagonal quadratic form `u ↦ c + (1/2) Σᵢ wᵢ uᵢ²` has derivative `v ↦ Σᵢ wᵢ uᵢ vᵢ`. -/
theorem hasFDerivAt_diagonalQuadratic {n : ℕ} (c : ℝ) (w u : Fin n → ℝ) :
    HasFDerivAt (fun u : Fin n → ℝ ↦ c + (2 : ℝ)⁻¹ * ∑ i, w i * (u i * u i))
      (∑ i, (w i * u i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) i) u := by
  have hp : ∀ i, HasFDerivAt (fun u : Fin n → ℝ ↦ u i)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) i) u :=
    fun i ↦ hasFDerivAt_apply i u
  have hs : HasFDerivAt (fun v : Fin n → ℝ ↦ ∑ i, w i * (v i * v i))
      (∑ i ∈ Finset.univ, w i • (u i • ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin n ↦ ℝ) i + u i • ContinuousLinearMap.proj i)) u :=
    HasFDerivAt.fun_sum fun i _ ↦ ((hp i).mul (hp i)).const_mul (w i)
  have h := (hs.const_mul (2 : ℝ)⁻¹).const_add c
  convert h using 1
  ext v
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, add_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

section DiagonalQuadratic

open Function

variable {ι : Type*} [Fintype ι]

/-- The **diagonal quadratic function** `∑ᵢ aᵢ xᵢ² / 2` on `ℝ^ι`, whose Hessian is diagonal with
eigenvalues `aᵢ`. -/
noncomputable def diagonalQuadratic (a : ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, a i * x i ^ 2 / 2

theorem diagonalQuadratic_apply (a x : ι → ℝ) :
    diagonalQuadratic a x = ∑ i, a i * x i ^ 2 / 2 :=
  (rfl)

theorem contDiff_diagonalQuadratic (a : ι → ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (diagonalQuadratic a) := by
  unfold diagonalQuadratic
  fun_prop

/-- The summands of a diagonal quadratic function, as functions of one variable. -/
private theorem deriv_mul_sq_div_two (c y : ℝ) : deriv (fun y : ℝ ↦ c * y ^ 2 / 2) y = c * y := by
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
  unfold diagonalQuadratic
  rw [fderiv_sum_comp_eval (φ := fun i y ↦ a i * y ^ 2 / 2) fun i ↦ by fun_prop]
  simp only [deriv_mul_sq_div_two, FunLike.coe_sum, Finset.sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- The Hessian of `∑ᵢ aᵢ xᵢ² / 2` is the diagonal form `∑ᵢ aᵢ vᵢ wᵢ`. -/
@[simp]
theorem fderiv_fderiv_diagonalQuadratic_apply (a x v w : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (diagonalQuadratic a)) x v w = ∑ i, a i * v i * w i := by
  unfold diagonalQuadratic
  rw [fderiv_fderiv_sum_comp_eval_apply (φ := fun i y ↦ a i * y ^ 2 / 2) fun i ↦ by fun_prop]
  simp [deriv_deriv_mul_sq_div_two]

end DiagonalQuadratic

end TauCeti
