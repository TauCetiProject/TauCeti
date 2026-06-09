/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Self-adjoint and skew-adjoint parts of real matrices

This file records the real square-matrix API for the decomposition of a matrix into its
self-adjoint and skew-adjoint parts, using Mathlib's `selfAdjointPart` and `skewAdjointPart`
star-module projections.
-/

namespace TauCeti

namespace Matrix

open _root_.Matrix

variable {n R : Type*}

/-- Mathlib's matrix quadratic form is the dot-product expression `ξᵀ A ξ`. -/
lemma toQuadraticForm'_eq_dotProduct [Fintype n] [DecidableEq n] [CommRing R]
    (A : Matrix n n R) (ξ : n → R) :
    A.toQuadraticForm' ξ = ξ ⬝ᵥ (A *ᵥ ξ) := by
  rw [_root_.Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, _root_.Matrix.toLinearMap₂'_apply']

variable {n : Type*}

/-- The self-adjoint part of a real square matrix is symmetric. -/
lemma isSymm_selfAdjointPart (A : Matrix n n ℝ) :
    (selfAdjointPart ℝ A : Matrix n n ℝ).IsSymm := by
  ext i j
  simp [selfAdjointPart_apply_coe, invOf_eq_inv, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, add_comm]
  ring

/-- The self-adjoint part is invariant under transpose. -/
@[simp]
lemma selfAdjointPart_transpose (A : Matrix n n ℝ) :
    (selfAdjointPart ℝ Aᵀ : Matrix n n ℝ) = (selfAdjointPart ℝ A : Matrix n n ℝ) := by
  ext i j
  simp [selfAdjointPart_apply_coe, invOf_eq_inv, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, add_comm]

/-- The skew-adjoint part changes sign under transpose. -/
@[simp]
lemma skewAdjointPart_transpose (A : Matrix n n ℝ) :
    (skewAdjointPart ℝ A : Matrix n n ℝ)ᵀ = -(skewAdjointPart ℝ A : Matrix n n ℝ) := by
  ext i j
  simp [skewAdjointPart_apply_coe, invOf_eq_inv, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, sub_eq_add_neg]

/-- A symmetric matrix is equal to its self-adjoint part. -/
@[simp]
lemma selfAdjointPart_eq_self_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm) :
    (selfAdjointPart ℝ A : Matrix n n ℝ) = A := by
  ext i j
  simp [selfAdjointPart_apply_coe, invOf_eq_inv, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, hA.apply]
  ring

/-- The self-adjoint part has the same diagonal bilinear form as the original matrix. -/
@[simp]
lemma dotProduct_selfAdjointPart_mulVec_self [Fintype n] (A : Matrix n n ℝ)
    (ξ : n → ℝ) :
    ξ ⬝ᵥ ((selfAdjointPart ℝ A : Matrix n n ℝ) *ᵥ ξ) = ξ ⬝ᵥ (A *ᵥ ξ) := by
  have hself :
      (selfAdjointPart ℝ A : Matrix n n ℝ) = (2 : ℝ)⁻¹ • (A + Aᵀ) := by
    ext i j
    simp [selfAdjointPart_apply_coe, invOf_eq_inv, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hself, smul_mulVec, dotProduct_smul, add_mulVec, dotProduct_add,
    _root_.Matrix.dotProduct_transpose_mulVec]
  ring

/-- The skew-adjoint part has zero diagonal bilinear form. -/
@[simp]
lemma dotProduct_skewAdjointPart_mulVec_self [Fintype n] (A : Matrix n n ℝ)
    (ξ : n → ℝ) :
    ξ ⬝ᵥ ((skewAdjointPart ℝ A : Matrix n n ℝ) *ᵥ ξ) = 0 := by
  have hskew :
      (skewAdjointPart ℝ A : Matrix n n ℝ) = (2 : ℝ)⁻¹ • (A - Aᵀ) := by
    ext i j
    simp [skewAdjointPart_apply_coe, invOf_eq_inv, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hskew, smul_mulVec, dotProduct_smul, sub_mulVec]
  have htranspose : ξ ⬝ᵥ (Aᵀ *ᵥ ξ) = ξ ⬝ᵥ (A *ᵥ ξ) :=
    by simpa using _root_.Matrix.dotProduct_transpose_mulVec (A := A) ξ ξ
  rw [dotProduct_sub, htranspose]
  ring

/-- The self-adjoint part has the same matrix quadratic form as the original matrix. -/
@[simp]
lemma toQuadraticForm'_selfAdjointPart [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (ξ : EuclideanSpace ℝ n) :
    (selfAdjointPart ℝ A : Matrix n n ℝ).toQuadraticForm' ξ = A.toQuadraticForm' ξ := by
  rw [toQuadraticForm'_eq_dotProduct, toQuadraticForm'_eq_dotProduct,
    dotProduct_selfAdjointPart_mulVec_self]

/-- The skew-adjoint part has zero matrix quadratic form. -/
@[simp]
lemma toQuadraticForm'_skewAdjointPart [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (ξ : EuclideanSpace ℝ n) :
    (skewAdjointPart ℝ A : Matrix n n ℝ).toQuadraticForm' ξ = 0 := by
  rw [toQuadraticForm'_eq_dotProduct, dotProduct_skewAdjointPart_mulVec_self]

end Matrix

end TauCeti
