/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.QuadraticForm.SepClosed

/-!
# Symmetric matrix congruence over a separably closed field

The orthonormal basis furnished by
`QuadraticForm.exists_toMatrix_eq_one_of_isSepClosed` gives a matrix congruence from a
nonsingular symmetric matrix to the identity in characteristic different from two.
-/

public section

open scoped Matrix

namespace Matrix.IsSymm

/-- Over a separably closed field of characteristic different from two, a nonsingular symmetric
matrix is congruent to the identity by an invertible matrix. -/
theorem exists_mul_mul_transpose_eq_one_of_isSepClosed {K ι : Type*} [Field K] [IsSepClosed K]
    [Invertible (2 : K)] [Fintype ι] [DecidableEq ι] {C : Matrix ι ι K} (hC : C.IsSymm)
    (hdet : C.det ≠ 0) :
    ∃ P : GL ι K, (P : Matrix ι ι K) * C * (P : Matrix ι ι K)ᵀ = 1 := by
  let B := C.toBilin'
  have hB : B.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hC
  have hassoc : B.toQuadraticMap.associated = B :=
    QuadraticMap.associated_left_inverse K hB.eq
  have hsep : B.toQuadraticMap.associated.SeparatingLeft := by
    rw [hassoc]
    exact (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet).1
  let b := Pi.basisFun K ι
  obtain ⟨w, hw⟩ :=
    QuadraticForm.exists_toMatrix_eq_one_of_isSepClosed B.toQuadraticMap hsep
  have hw' : B.toMatrix w = 1 := by
    simpa only [QuadraticForm.toMatrix, LinearMap.BilinForm.toMatrix, hassoc] using hw
  let e := w.indexEquiv b
  let v := w.reindex e
  have hv : B.toMatrix v = 1 := by
    ext i j
    have h := congrFun (congrFun hw' (e.symm i)) (e.symm j)
    simpa only [LinearMap.BilinForm.toMatrix_apply, Matrix.one_apply, v,
      Module.Basis.reindex_apply, e.symm.injective.eq_iff] using h
  have hcoord := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b v B
  rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin', hv] at hcoord
  let _ := b.invertibleToMatrix v
  let U : GL ι K := unitOfInvertible (b.toMatrix v)
  exact ⟨(GeneralLinearGroup.transposeMulEquiv ι U).unop, by
    rw [GeneralLinearGroup.coe_unop_transposeMulEquiv, transpose_transpose]
    exact hcoord⟩

end Matrix.IsSymm
