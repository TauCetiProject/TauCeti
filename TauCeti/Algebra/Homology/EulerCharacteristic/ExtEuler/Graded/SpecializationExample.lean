/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.Algebra.Polynomial.Laurent.Basic

/-!
# Degeneracy of a specialized Laurent-polynomial pairing

Specializing a Laurent-polynomial-valued pairing can destroy nondegeneracy. The matrix
`!![1, 1; 1, q]` has nonzero determinant over `ℤ[q,q⁻¹]`, while its specialization at `q = 1`
has the nonzero vector `(1, -1)` in its kernel. This is the elementary matrix example behind the
specialization warning for graded Euler forms.

The q-Euler convention and specialization context follow Dancso and Licata, “Koszul algebras and
flow lattices,” Sections 1.2 and 3.1--3.2.
-/

public section

namespace TauCeti

open LaurentPolynomial Matrix

noncomputable section

/-- A Laurent-polynomial matrix with nonzero determinant that becomes degenerate at `q = 1`. -/
def specializationDegeneracyMatrix : Matrix (Fin 2) (Fin 2) (LaurentPolynomial ℤ) :=
  !![1, 1; 1, T 1]

/-- The determinant of the specialization example is `q - 1`. -/
theorem det_specializationDegeneracyMatrix :
    specializationDegeneracyMatrix.det = T 1 - 1 := by
  simp [specializationDegeneracyMatrix, Matrix.det_fin_two_of]

/-- The determinant of the Laurent-polynomial matrix is nonzero before specialization. -/
theorem det_specializationDegeneracyMatrix_ne_zero :
    specializationDegeneracyMatrix.det ≠ 0 := by
  rw [det_specializationDegeneracyMatrix]
  intro h
  have hc := congrArg (fun p : LaurentPolynomial ℤ => p.coeff 1) h
  change (T 1).coeff 1 - (1 : LaurentPolynomial ℤ).coeff 1 = 0 at hc
  rw [LaurentPolynomial.T_apply] at hc
  have hconst : (1 : LaurentPolynomial ℤ).coeff 1 = 0 := by
    change Finsupp.single (0 : ℤ) (1 : ℤ) 1 = 0
    simp
  rw [hconst] at hc
  norm_num at hc

/-- The matrix after evaluation at `q = 1`, with entries in `ℤ`. -/
def specializationDegeneracyMatrixAtOne : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 1, 1]

/-- The specialized matrix is obtained by evaluating every entry of the Laurent matrix at `1`. -/
theorem specializationDegeneracyMatrixAtOne_eq_map :
    specializationDegeneracyMatrixAtOne =
      specializationDegeneracyMatrix.map (laurentEval (R := ℤ) (1 : ℤˣ)).toRingHom := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [specializationDegeneracyMatrixAtOne, specializationDegeneracyMatrix, laurentEval_T]

/-- The specialized matrix has zero determinant. -/
theorem det_specializationDegeneracyMatrixAtOne :
    specializationDegeneracyMatrixAtOne.det = 0 := by
  simp [specializationDegeneracyMatrixAtOne, Matrix.det_fin_two_of]

/-- The vector `(1, -1)` witnesses degeneracy of the matrix at `q = 1`. -/
theorem specializationDegeneracyMatrixAtOne_mulVec_kernel :
    specializationDegeneracyMatrixAtOne *ᵥ (![1, -1] : Fin 2 → ℤ) = 0 := by
  ext i
  fin_cases i <;> simp [specializationDegeneracyMatrixAtOne, Matrix.mulVec]

/-- The specialization kernel vector is nonzero. -/
theorem specializationDegeneracyMatrixAtOne_kernelVector_ne_zero :
    (![1, -1] : Fin 2 → ℤ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num at h0

end

end TauCeti
