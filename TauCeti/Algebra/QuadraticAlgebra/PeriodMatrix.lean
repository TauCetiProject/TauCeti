/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.QuadraticAlgebra

/-!
# Quadratic multiplication in period coordinates

The native regular representation of a quadratic algebra uses column coordinates in the basis
`(1, ω)`. This file reverses the basis and transposes to row coordinates in `(ω, 1)`, as used for
complex period lattices and their division points. The construction preserves multiplication;
its determinant is the quadratic norm, so invertible matrices correspond to actual units.
It works over every commutative ring, including the residue rings used for finite-level actions.

## References

* D. H. Shin, *Generation of class fields by Siegel-Ramachandra invariants*, §2, for the
  multiplication matrices in the row-coordinate convention.
-/

public section

noncomputable section

open Matrix

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- The regular multiplication matrix in row coordinates ordered as `(ω, 1)`. -/
def periodMulMatrix (z : QuadraticAlgebra R a b) : Matrix (Fin 2) (Fin 2) R :=
  (Algebra.leftMulMatrix (basis a b) z).transpose.submatrix Fin.revPerm Fin.revPerm

/-- The identity scalar has the identity period matrix. -/
@[simp]
theorem periodMulMatrix_one : (1 : QuadraticAlgebra R a b).periodMulMatrix = 1 := by
  simp only [periodMulMatrix, map_one, Matrix.transpose_one]
  exact Matrix.submatrix_one_equiv Fin.revPerm

/-- Period matrices compose in the order of their right action on row coordinates. -/
@[simp]
theorem periodMulMatrix_mul (z w : QuadraticAlgebra R a b) :
    (z * w).periodMulMatrix = z.periodMulMatrix * w.periodMulMatrix := by
  rw [mul_comm z w]
  simp only [periodMulMatrix, map_mul, Matrix.transpose_mul]
  exact (Matrix.submatrix_mul_equiv _ _ Fin.revPerm Fin.revPerm Fin.revPerm).symm

/-- Multiplication in period coordinates, bundled as a monoid homomorphism. -/
def periodMulMatrixHom : QuadraticAlgebra R a b →* Matrix (Fin 2) (Fin 2) R where
  toFun := periodMulMatrix
  map_one' := periodMulMatrix_one
  map_mul' := periodMulMatrix_mul

/-- The bundled period representation evaluates to the specified multiplication matrix. -/
@[simp]
theorem periodMulMatrixHom_apply (z : QuadraticAlgebra R a b) :
    periodMulMatrixHom z = z.periodMulMatrix := (by rfl)

/-- The row multiplication matrix has the coefficients used for quadratic division points. -/
theorem periodMulMatrix_eq (z : QuadraticAlgebra R a b) :
    z.periodMulMatrix = !![z.re + b * z.im, a * z.im; z.im, z.re] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [periodMulMatrix, Algebra.leftMulMatrix_quadraticAlgebra]

/-- The determinant is the norm of the quadratic element. -/
@[simp]
theorem det_periodMulMatrix (z : QuadraticAlgebra R a b) :
    z.periodMulMatrix.det = z.norm := by
  rw [periodMulMatrix, Matrix.det_submatrix_equiv_self, Matrix.det_transpose,
    ← Algebra.norm_eq_matrix_det, Algebra.norm_quadraticAlgebra_apply]

/-- An invertible period matrix comes exactly from a unit of the quadratic algebra. -/
@[simp]
theorem isUnit_periodMulMatrix_iff (z : QuadraticAlgebra R a b) :
    IsUnit z.periodMulMatrix ↔ IsUnit z := by
  rw [Matrix.isUnit_iff_isUnit_det, det_periodMulMatrix, isUnit_iff_norm_isUnit]

/-- The bottom row recovers the element, so the period representation is faithful. -/
theorem periodMulMatrix_injective :
    Function.Injective (periodMulMatrix : QuadraticAlgebra R a b → Matrix (Fin 2) (Fin 2) R) := by
  intro z w h
  have him := congrArg (fun M => M 1 0) h
  have hre := congrArg (fun M => M 1 1) h
  simp only [periodMulMatrix_eq, of_apply, cons_val_one, cons_val_zero] at him hre
  exact QuadraticAlgebra.ext hre him

/-- Changing coefficients commutes with the period representation. In particular this identifies
reduction of integral multiplication matrices with multiplication in the residue algebra. -/
@[simp]
theorem periodMulMatrix_mapRingHom {S : Type*} [CommRing S] (f : R →+* S)
    (z : QuadraticAlgebra R a b) :
    (mapRingHom f a b z).periodMulMatrix = z.periodMulMatrix.map f := by
  rw [periodMulMatrix_eq, periodMulMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mapRingHom]

end QuadraticAlgebra
