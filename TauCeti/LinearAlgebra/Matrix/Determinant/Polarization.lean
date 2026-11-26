/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.Matrix.Adjugate.FinTwo
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.Matrix.Determinant.FinFour
import TauCeti.LinearAlgebra.PerfectPairing.Basis

/-!
# The determinant pairing on two-by-two matrices

The determinant on two-by-two matrices polarizes to a symmetric perfect pairing over a
commutative ring. It pairs opposite matrix units with signs, and left and right multiplication
scale the pairing by the corresponding determinants. In particular the pairing identifies the
matrix module with its dual in characteristic two as well.

This is the matrix pairing used in Gal Dor, [*Exotic Monoidal Structures and Abstractly
Automorphic Representations for GL(2)*](https://doi.org/10.1017/fmp.2023.18), Construction 2.7.
-/

public section

namespace Matrix

open LinearMap (BilinForm)

variable {R : Type*} [CommRing R]

/-- The polarization of the two-by-two determinant, realized as `(A, B) ↦ tr (adj A * B)`
using `Matrix.adjugateFinTwoLinearMap`. -/
noncomputable def detFinTwoBilin (R : Type*) [CommRing R] :
    BilinForm R (Matrix (Fin 2) (Fin 2) R) :=
  ((LinearMap.mul R _).compr₂ (traceLinearMap (Fin 2) R R)).compl₁₂
    adjugateFinTwoLinearMap LinearMap.id

/-- The determinant pairing in trace coordinates. -/
theorem detFinTwoBilin_apply (A B : Matrix (Fin 2) (Fin 2) R) :
    detFinTwoBilin R A B = A.trace * B.trace - (A * B).trace := by
  simpa only [detFinTwoBilin, LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, LinearMap.id_apply,
    LinearMap.mul_apply', traceLinearMap_apply, adjugateFinTwoLinearMap_apply] using
    trace_adjugate_mul_fin_two A B

/-- The determinant pairing in entry coordinates. -/
theorem detFinTwoBilin_apply_entries (A B : Matrix (Fin 2) (Fin 2) R) :
    detFinTwoBilin R A B = A 0 0 * B 1 1 + A 1 1 * B 0 0 - A 0 1 * B 1 0 - A 1 0 * B 0 1 := by
  simp only [detFinTwoBilin_apply, trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The determinant pairing is the unscaled polarization of the determinant. -/
theorem detFinTwoBilin_apply_eq_det (A B : Matrix (Fin 2) (Fin 2) R) :
    detFinTwoBilin R A B = (A + B).det - A.det - B.det := by
  simp only [detFinTwoBilin_apply_entries, det_fin_two, Matrix.add_apply]
  ring

/-- The determinant pairing is symmetric. -/
theorem isSymm_detFinTwoBilin : (detFinTwoBilin R).IsSymm :=
  ⟨fun A B ↦ by simp only [detFinTwoBilin_apply, trace_mul_comm B A, mul_comm B.trace A.trace]⟩

/-- The pairing on the diagonal is twice the determinant. -/
@[simp]
theorem detFinTwoBilin_apply_self (A : Matrix (Fin 2) (Fin 2) R) :
    detFinTwoBilin R A A = 2 * A.det := by
  simp only [detFinTwoBilin_apply_entries, det_fin_two]
  ring

/-- Simultaneous transpose preserves the determinant pairing. -/
@[simp]
theorem detFinTwoBilin_transpose (A B : Matrix (Fin 2) (Fin 2) R) :
    detFinTwoBilin R Aᵀ Bᵀ = detFinTwoBilin R A B := by
  simp only [detFinTwoBilin_apply_eq_det, ← transpose_add, det_transpose]

/-- Left and right matrix multiplication act on the determinant pairing by the product of their
determinants. This identity also holds for singular multipliers. -/
theorem detFinTwoBilin_mul_mul (L M A B : Matrix (Fin 2) (Fin 2) R) :
    detFinTwoBilin R (L * A * M) (L * B * M) = (L.det * M.det) * detFinTwoBilin R A B := by
  simp only [detFinTwoBilin_apply_eq_det, ← Matrix.add_mul, ← Matrix.mul_add, det_mul]
  ring

/-- The Gram matrix of the determinant pairing in the row-major order of matrix units. -/
theorem toMatrix_detFinTwoBilin :
    (detFinTwoBilin R).toMatrix ((stdBasis R (Fin 2) (Fin 2)).reindex finProdFinEquiv) =
      !![0, 0, 0, 1; 0, 0, -1, 0; 0, -1, 0, 0; 1, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-detFinTwoBilin_apply_self, detFinTwoBilin_apply_entries, finProdFinEquiv,
      Fin.divNat, Fin.modNat, stdBasis_eq_single]

/-- The determinant of the Gram matrix in the standard matrix basis is one. -/
@[simp]
theorem det_toMatrix_detFinTwoBilin :
    ((detFinTwoBilin R).toMatrix (stdBasis R (Fin 2) (Fin 2))).det = 1 := by
  rw [← BilinForm.det_toMatrix_reindex (stdBasis R (Fin 2) (Fin 2)) finProdFinEquiv,
    toMatrix_detFinTwoBilin, det_fin_four]
  simp

/-- The determinant pairing is perfect over every commutative ring. Its canonical duality
isomorphism is `LinearMap.toPerfPair`. -/
instance instIsPerfPairDetFinTwoBilin : (detFinTwoBilin R).IsPerfPair :=
  let b := stdBasis R (Fin 2) (Fin 2)
  b.isPerfPair_of_isUnit_det b _ (by
    rw [← LinearMap.BilinForm.toMatrix, det_toMatrix_detFinTwoBilin]
    exact isUnit_one)

end Matrix
