/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Coordinate action of unitary matrices

`Matrix.UnitaryGroup.toLinearEquiv_apply` describes the linear equivalence associated to a unitary
matrix by its matrix-vector action.

Permutation matrices are unitary (`Matrix.permMatrix_mem_unitaryGroup`), and
`Matrix.UnitaryGroup.permMatrixHom` is `Matrix.permMatrixHom` with its values in the unitary group.
-/

public section

universe u v

namespace Matrix.UnitaryGroup

variable {R : Type u} [CommRing R] [StarRing R]
variable {n : Type v} [Fintype n] [DecidableEq n]

/-- The linear equivalence associated to a unitary matrix acts by matrix-vector
multiplication. -/
@[simp]
theorem toLinearEquiv_apply (U : Matrix.unitaryGroup n R) (x : n → R) :
    Matrix.UnitaryGroup.toLinearEquiv U x = Matrix.toLin' (U : Matrix n n R) x := rfl

/-- A permutation matrix is unitary. -/
theorem _root_.Matrix.permMatrix_mem_unitaryGroup (σ : Equiv.Perm n) :
    σ.permMatrix R ∈ Matrix.unitaryGroup n R := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_permMatrix, ← permMatrix_mul,
    inv_mul_cancel, permMatrix_one]

/-- Permutation matrices as elements of the unitary group. As for `Matrix.permMatrixHom`, the
permutation `σ` goes to the permutation matrix of `σ⁻¹`, which makes this a homomorphism for
Mathlib's convention for multiplication in `Equiv.Perm`. -/
def permMatrixHom : Equiv.Perm n →* Matrix.unitaryGroup n R :=
  (Matrix.permMatrixHom (R := R)).codRestrict (Matrix.unitaryGroup n R) fun σ => by
    rw [permMatrixHom_apply]
    exact Matrix.permMatrix_mem_unitaryGroup σ⁻¹

/-- As a matrix, `Matrix.UnitaryGroup.permMatrixHom σ` is the permutation matrix of `σ⁻¹`. -/
@[simp]
theorem coe_permMatrixHom (σ : Equiv.Perm n) :
    (permMatrixHom (R := R) σ : Matrix n n R) = σ⁻¹.permMatrix R :=
  (rfl)

end Matrix.UnitaryGroup

