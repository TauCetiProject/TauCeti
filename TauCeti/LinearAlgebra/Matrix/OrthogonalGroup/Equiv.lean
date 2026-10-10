/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm

/-!
# The standard quadratic orthogonal group in matrix coordinates

When two is a regular scalar, taking the matrix of a linear automorphism identifies the
orthogonal group of the standard quadratic form with `Matrix.orthogonalGroup`. This bundles
the coordinate membership criterion `TauCeti.toMatrix_mem_orthogonalGroup_iff` into a group
isomorphism. Its inverse acts by matrix-vector multiplication, and the isomorphism preserves
the determinant. These equations let abstract quadratic-space calculations use the classical
matrix orthogonal group without unfolding either carrier.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance] starRingOfComm

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- The orthogonal group of the standard quadratic form is the matrix orthogonal group,
provided multiplication by two is injective. -/
noncomputable def standardOrthogonalGroupEquiv (h2 : IsSMulRegular R (2 : R)) :
    QuadraticMap.orthogonalGroup (Matrix.toQuadraticForm' (1 : Matrix n n R)) ≃*
      Matrix.orthogonalGroup n R where
  toFun g := ⟨LinearMap.toMatrix' (g : (n → R) ≃ₗ[R] (n → R)).toLinearMap,
    (toMatrix_mem_orthogonalGroup_iff R n h2 _).mpr g.2⟩
  invFun A := ⟨Matrix.UnitaryGroup.toLinearEquiv A,
    (toMatrix_mem_orthogonalGroup_iff R n h2 _).mp (by
      simp [Matrix.UnitaryGroup.toLinearEquiv])⟩
  left_inv g := Subtype.ext <| LinearEquiv.ext fun x ↦ by
    simp [Matrix.UnitaryGroup.toLinearEquiv]
  right_inv A := Subtype.ext <| by simp [Matrix.UnitaryGroup.toLinearEquiv]
  map_mul' g h := Subtype.ext <| by
    simpa using LinearMap.toMatrix'_mul
      (g : (n → R) ≃ₗ[R] (n → R)).toLinearMap
      (h : (n → R) ≃ₗ[R] (n → R)).toLinearMap

/-- The standard orthogonal comparison takes the coordinate matrix of an automorphism. -/
@[simp]
theorem coe_standardOrthogonalGroupEquiv_apply (h2 : IsSMulRegular R (2 : R))
    (g : QuadraticMap.orthogonalGroup (Matrix.toQuadraticForm' (1 : Matrix n n R))) :
    (standardOrthogonalGroupEquiv h2 g : Matrix n n R) =
      LinearMap.toMatrix' (g : (n → R) ≃ₗ[R] (n → R)).toLinearMap := (rfl)

/-- The inverse standard orthogonal comparison acts by matrix-vector multiplication. -/
@[simp]
theorem standardOrthogonalGroupEquiv_symm_apply (h2 : IsSMulRegular R (2 : R))
    (A : Matrix.orthogonalGroup n R) (x : n → R) :
    ((standardOrthogonalGroupEquiv h2).symm A : (n → R) ≃ₗ[R] (n → R)) x =
      (A : Matrix n n R) *ᵥ x := (rfl)

end TauCeti
