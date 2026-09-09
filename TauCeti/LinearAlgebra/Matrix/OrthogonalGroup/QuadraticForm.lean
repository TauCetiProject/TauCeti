/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Quadratic and matrix orthogonal groups

When two is invertible in the base ring, a linear automorphism preserves the standard
quadratic form exactly when its matrix is orthogonal. Adding determinant one identifies the
two special orthogonal groups. These criteria transfer quadratic-space results to the matrix
models of the classical groups.

The proof uses the Gram-matrix criterion `TauCeti.BilinForm.isIsometry_iff_toMatrix` and
Mathlib's compatibility of the associated bilinear form with composition.
-/

public section

namespace TauCeti

open Matrix

universe u v

/-- The coordinate matrix of a linear automorphism is orthogonal exactly when the
automorphism preserves the standard quadratic form. -/
theorem toMatrix_mem_orthogonalGroup_iff (R : Type u) [CommRing R]
    (n : Type v) [Fintype n] [DecidableEq n] [Invertible (2 : R)]
    (e : (n → R) ≃ₗ[R] (n → R)) :
    LinearMap.toMatrix' e.toLinearMap ∈ Matrix.orthogonalGroup n R ↔
      e ∈ QuadraticMap.orthogonalGroup (Matrix.toQuadraticForm' (1 : Matrix n n R)) := by
  let B : LinearMap.BilinForm R (n → R) := Matrix.toLinearMap₂' R (1 : Matrix n n R)
  have hgram :
      BilinForm.IsIsometry B e.toLinearMap ↔
        LinearMap.toMatrix' e.toLinearMap ∈ Matrix.orthogonalGroup n R := by
    rw [BilinForm.isIsometry_iff_toMatrix (Pi.basisFun R n)]
    simp only [B, LinearMap.toMatrix_eq_toMatrix', LinearMap.BilinForm.toMatrix_basisFun,
      LinearMap.BilinForm.toMatrix', LinearMap.toMatrix'_toLinearMap₂', mul_one,
      Matrix.mem_orthogonalGroup_iff']
  rw [← hgram, QuadraticMap.mem_orthogonalGroup_iff]
  constructor
  · intro he x
    exact he.apply x x
  · intro he
    have hcomp :
        (Matrix.toQuadraticForm' (1 : Matrix n n R)).comp e.toLinearMap =
          Matrix.toQuadraticForm' (1 : Matrix n n R) := by
      ext x
      exact he x
    have hassoc := congrArg (QuadraticMap.associatedHom R) hcomp
    have hB : (Matrix.toQuadraticForm' (1 : Matrix n n R)).associated = B := by
      apply QuadraticMap.associated_left_inverse
      intro x y
      simpa only [Matrix.toLinearMap₂'_apply', Matrix.one_mulVec] using dotProduct_comm x y
    rw [QuadraticMap.associated_comp, hB] at hassoc
    exact BilinForm.isIsometry_iff.mpr (fun x y ↦ DFunLike.congr_fun
      (DFunLike.congr_fun hassoc x) y)

/-- The coordinate matrix is special orthogonal exactly when the linear automorphism is
special orthogonal for the standard quadratic form. -/
theorem toMatrix_mem_specialOrthogonalGroup_iff (R : Type u) [CommRing R]
    (n : Type v) [Fintype n] [DecidableEq n] [Invertible (2 : R)]
    (e : (n → R) ≃ₗ[R] (n → R)) :
    LinearMap.toMatrix' e.toLinearMap ∈ Matrix.specialOrthogonalGroup n R ↔
      e ∈ QuadraticMap.specialOrthogonalGroup
        (Matrix.toQuadraticForm' (1 : Matrix n n R)) := by
  rw [Matrix.mem_specialOrthogonalGroup_iff, toMatrix_mem_orthogonalGroup_iff,
    QuadraticMap.mem_specialOrthogonalGroup_iff, LinearMap.det_toMatrix',
    ← LinearEquiv.coe_det]
  simp only [Units.val_eq_one]

end TauCeti
