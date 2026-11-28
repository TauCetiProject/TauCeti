/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Conjugation of lists of matrices

Summing a list of square matrices commutes with conjugation, and so does the product of the
exponentials of the list.

## Main results

* `Matrix.list_sum_map_conj`: `(L.map fun A ↦ U * A * U⁻¹).sum = U * L.sum * U⁻¹`.
* `Matrix.list_prod_map_exp_conj`: `∏ exp (U * A * U⁻¹) = U * (∏ exp A) * U⁻¹` for invertible `U`.
-/

public section

open NormedSpace

namespace Matrix

section Sum

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Summation commutes with conjugation: the sum of `U * A * U⁻¹` over a list `L` is
`U * (∑ L) * U⁻¹`. -/
theorem list_sum_map_conj (U : Matrix n n R) (L : List (Matrix n n R)) :
    (L.map fun A ↦ U * A * U⁻¹).sum = U * L.sum * U⁻¹ := by
  rw [List.sum_map_mul_right, List.sum_map_mul_left, List.map_id']

end Sum

section Exp

variable {m 𝔸 : Type*} [Fintype m] [DecidableEq m] [NormedCommRing 𝔸] [NormedAlgebra ℚ 𝔸]
  [CompleteSpace 𝔸]

/-- Conjugation by an invertible matrix passes inside a product of matrix exponentials. -/
theorem list_prod_map_exp_conj {U : Matrix m m 𝔸} (hU : IsUnit U) (L : List (Matrix m m 𝔸)) :
    ((L.map fun A ↦ U * A * U⁻¹).map exp).prod = U * (L.map exp).prod * U⁻¹ := by
  have hUU : U⁻¹ * U = 1 := nonsing_inv_mul U ((isUnit_iff_isUnit_det U).mp hU)
  have hmul (X Y : Matrix m m 𝔸) :
      (U * X * U⁻¹) * (U * Y * U⁻¹) = U * (X * Y) * U⁻¹ := by
    simp only [mul_assoc]
    rw [← mul_assoc U⁻¹ U (Y * U⁻¹), hUU, one_mul]
  induction L with
  | nil =>
    simp only [List.map_nil, List.prod_nil, mul_one]
    exact (mul_nonsing_inv U ((isUnit_iff_isUnit_det U).mp hU)).symm
  | cons A L ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [exp_conj U A hU, ih, hmul]

end Exp

end Matrix
