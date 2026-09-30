/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import TauCeti.Algebra.Polynomial.Laurent.Basic

/-!
# A Laurent matrix whose specializations are degenerate

The matrix `[[1,1],[1,q]]` has nonzero determinant `q - 1`, but at `q = 1` its rows coincide.
Replacing `q` by `-q` gives the same phenomenon at `q = -1`. These two small examples show why
nondegeneracy of a Laurent-valued Euler pairing cannot be carried through either specialization
without an additional hypothesis. The matrices are algebraic examples; no category is claimed to
realize them as an Ext-Euler matrix.
-/

public section

namespace TauCeti

open LaurentPolynomial
open scoped Matrix

private noncomputable def specializationMatrix (p : LaurentPolynomial ℤ) :
    Matrix (Fin 2) (Fin 2) (LaurentPolynomial ℤ) :=
  !![1, 1; 1, p]

private theorem specializationMatrix_det (p : LaurentPolynomial ℤ) :
    (specializationMatrix p).det = p - 1 := by
  simp [specializationMatrix, Matrix.det_fin_two_of]

private theorem specializationMatrix_eval_one (p : LaurentPolynomial ℤ) (ε : ℤˣ)
    (hp : laurentEval ε p = 1) :
    (specializationMatrix p).map (laurentEval ε) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [specializationMatrix, hp]

/-- The matrix `[[1,1],[1,q]]` over `ℤ[q,q⁻¹]`. Its determinant is `q - 1`, so it is
nondegenerate over the Laurent-polynomial domain, while its specialization at `q = 1` is
degenerate. -/
noncomputable def laurentMatrixDegenerateAtOne : Matrix (Fin 2) (Fin 2) (LaurentPolynomial ℤ) :=
  specializationMatrix (T 1)

/-- The matrix `[[1,1],[1,-q]]` over `ℤ[q,q⁻¹]`. Its determinant is `-q - 1`, so it is
nondegenerate over the Laurent-polynomial domain, while its specialization at `q = -1` is
degenerate. -/
noncomputable def laurentMatrixDegenerateAtNegOne :
    Matrix (Fin 2) (Fin 2) (LaurentPolynomial ℤ) :=
  specializationMatrix (-(T 1))

/-- The determinant `q - 1` is a nonzero Laurent polynomial. -/
theorem laurentMatrixDegenerateAtOne_det_ne_zero :
    laurentMatrixDegenerateAtOne.det ≠ 0 := by
  rw [laurentMatrixDegenerateAtOne, specializationMatrix_det]
  intro h
  have he := congrArg (laurentEval (-1 : ℤˣ)) h
  norm_num [laurentEval_T_one] at he

/-- The determinant `-q - 1` is a nonzero Laurent polynomial. -/
theorem laurentMatrixDegenerateAtNegOne_det_ne_zero :
    laurentMatrixDegenerateAtNegOne.det ≠ 0 := by
  rw [laurentMatrixDegenerateAtNegOne, specializationMatrix_det]
  intro h
  have he := congrArg (laurentEval (1 : ℤˣ)) h
  norm_num [laurentEval_T_one] at he

/-- The first Laurent matrix has trivial right kernel before specialization. -/
theorem laurentMatrixDegenerateAtOne_mulVec_injective :
    Function.Injective laurentMatrixDegenerateAtOne.mulVec :=
  Matrix.mulVec_injective_of_det_ne_zero laurentMatrixDegenerateAtOne_det_ne_zero

/-- The second Laurent matrix has trivial right kernel before specialization. -/
theorem laurentMatrixDegenerateAtNegOne_mulVec_injective :
    Function.Injective laurentMatrixDegenerateAtNegOne.mulVec :=
  Matrix.mulVec_injective_of_det_ne_zero laurentMatrixDegenerateAtNegOne_det_ne_zero

/-- The determinant vanishes after evaluation at `q = 1`. -/
theorem laurentMatrixDegenerateAtOne_specialization_det_eq_zero :
    (laurentMatrixDegenerateAtOne.map (laurentEval (1 : ℤˣ))).det = 0 := by
  rw [laurentMatrixDegenerateAtOne,
    specializationMatrix_eval_one (T 1) 1 (by simp)]
  norm_num [Matrix.det_fin_two_of]

/-- The determinant vanishes after evaluation at `q = -1`. -/
theorem laurentMatrixDegenerateAtNegOne_specialization_det_eq_zero :
    (laurentMatrixDegenerateAtNegOne.map (laurentEval (-1 : ℤˣ))).det = 0 := by
  rw [laurentMatrixDegenerateAtNegOne,
    specializationMatrix_eval_one (-(T 1)) (-1) (by simp)]
  norm_num [Matrix.det_fin_two_of]

/-- At `q = 1`, the two rows coincide, so the specialized matrix has nontrivial kernel. -/
theorem laurentMatrixDegenerateAtOne_specialization_has_kernel :
    ∃ v : Fin 2 → ℤ, v ≠ 0 ∧
      (laurentMatrixDegenerateAtOne.map (laurentEval (1 : ℤˣ))).mulVec v = 0 :=
  Matrix.exists_mulVec_eq_zero_iff.mpr
    laurentMatrixDegenerateAtOne_specialization_det_eq_zero

/-- At `q = -1`, the two rows coincide, so the specialized matrix has nontrivial kernel. -/
theorem laurentMatrixDegenerateAtNegOne_specialization_has_kernel :
    ∃ v : Fin 2 → ℤ, v ≠ 0 ∧
      (laurentMatrixDegenerateAtNegOne.map (laurentEval (-1 : ℤˣ))).mulVec v = 0 :=
  Matrix.exists_mulVec_eq_zero_iff.mpr
    laurentMatrixDegenerateAtNegOne_specialization_det_eq_zero

end TauCeti
