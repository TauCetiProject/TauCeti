/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The dilations in `SL(2, ℝ)`

The diagonal matrices `dilation s = !![exp (s / 2), 0; 0, exp (-(s / 2))]` form a one-parameter
subgroup of `SL(2, ℝ)` (`dilation_zero`, `dilation_add`, `dilation_inv`): the positive component
of the diagonal subgroup of `SL(2, ℝ)`, parametrised by the logarithm of the eigenvalue ratio.
Acting on the upper half-plane by Möbius transformations they are the dilations
`z ↦ exp s * z`, which is why the parameter is `s` rather than the eigenvalue `exp (s / 2)`:
`dilation s` moves a point of the imaginary axis upward by the signed displacement `s`, that is,
by hyperbolic distance `|s|`, upward for `s > 0` and downward for `s < 0`.

## Main declarations

* `Matrix.SpecialLinearGroup.dilation`: the dilation matrix, with entries `coe_dilation`.
* `Matrix.SpecialLinearGroup.dilation_add`, `dilation_inv`: the family is a one-parameter
  subgroup.
* `Matrix.SpecialLinearGroup.eq_dilation_two_mul_log`: every diagonal matrix of `SL(2, ℝ)` with
  positive entries is a dilation.
-/

public section

noncomputable section

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

/-- The dilation `!![exp (s / 2), 0; 0, exp (-(s / 2))]`, an element of `SL(2, ℝ)` acting on `ℍ`
as `z ↦ exp s * z`. -/
def dilation (s : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.exp (s / 2), 0; 0, Real.exp (-(s / 2))], by
    rw [Matrix.det_fin_two_of]
    simp [← Real.exp_add]⟩

/-- The entries of `dilation s`. -/
@[simp]
theorem coe_dilation (s : ℝ) :
    (dilation s : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.exp (s / 2), 0; 0, Real.exp (-(s / 2))] :=
  (rfl)

/-- The dilation by `0` is the identity. -/
@[simp]
theorem dilation_zero : dilation 0 = 1 :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ by
    fin_cases i <;> fin_cases j <;> simp

/-- The dilations form a one-parameter subgroup: `dilation (s + t) = dilation s * dilation t`. -/
theorem dilation_add (s t : ℝ) : dilation (s + t) = dilation s * dilation t :=
  Matrix.SpecialLinearGroup.ext _ _ fun i j ↦ by
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← Real.exp_add, add_div, add_comm]

/-- The inverse of `dilation s` is `dilation (-s)`. -/
@[simp]
theorem dilation_inv (s : ℝ) : (dilation s)⁻¹ = dilation (-s) :=
  inv_eq_of_mul_eq_one_right (by rw [← dilation_add, add_neg_cancel, dilation_zero])

/-- A diagonal matrix of `SL(2, ℝ)` with positive entries is a dilation: the one by twice the
logarithm of its top-left entry. -/
theorem eq_dilation_two_mul_log {A : SL(2, ℝ)} (h₁₀ : A 1 0 = 0) (h₀₁ : A 0 1 = 0)
    (hpos : 0 < A 0 0) : A = dilation (2 * Real.log (A 0 0)) := by
  have hdet := A.det_coe
  rw [Matrix.det_fin_two, h₁₀, h₀₁, mul_zero, sub_zero] at hdet
  have h₁₁ : A 1 1 = (A 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h₁₀, h₀₁, h₁₁, Real.exp_neg, Real.exp_log hpos]

end Matrix.SpecialLinearGroup
