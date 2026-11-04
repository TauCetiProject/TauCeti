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
matrix by its matrix-vector action, and `Matrix.permMatrix_mem_unitaryGroup` records that
permutation matrices are unitary. Accordingly `Matrix.permutationUnitary` is
`Matrix.permMatrixHom` with values in the unitary group.

`Matrix.conjTranspose_mul_mul_mem_unitary` transfers unitarity along a possibly rectangular
matrix whose conjugate transpose is a two-sided inverse.
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

end Matrix.UnitaryGroup

namespace Matrix

/-- Conjugation by a possibly rectangular matrix with conjugate-transpose inverse preserves
unitarity over a possibly noncommutative star semiring. -/
theorem conjTranspose_mul_mul_mem_unitary
    {R m n : Type*} [Semiring R] [StarRing R]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (P : Matrix m n R) (hP : Pᴴ * P = 1) (hP' : P * Pᴴ = 1)
    {X : Matrix m m R} (hX : X ∈ unitary (Matrix m m R)) :
    Pᴴ * X * P ∈ unitary (Matrix n n R) := by
  have hcancel (Y Z : Matrix m m R) :
      (Pᴴ * Y * P) * (Pᴴ * Z * P) = Pᴴ * (Y * Z) * P := by
    calc
      _ = Pᴴ * (Y * (P * Pᴴ) * Z) * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP', Matrix.mul_one]
  rw [Unitary.mem_iff, star_eq_conjTranspose] at hX ⊢
  constructor <;>
    simp only [conjTranspose_mul, conjTranspose_conjTranspose,
      ← Matrix.mul_assoc Pᴴ Xᴴ P, hcancel, hX.1, hX.2, Matrix.mul_one, hP]

variable {R : Type u} [CommRing R] [StarRing R]
variable {n : Type v} [Fintype n] [DecidableEq n]

/-- A permutation matrix is unitary: its conjugate transpose is the permutation matrix of the
inverse permutation. -/
theorem permMatrix_mem_unitaryGroup (σ : Equiv.Perm n) :
    σ.permMatrix R ∈ unitaryGroup n R := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_permMatrix, ← permMatrix_mul,
    inv_mul_cancel, permMatrix_one]

/-- A permutation as a unitary matrix: `permutationUnitary σ` is the permutation matrix of `σ⁻¹`,
which makes this a homomorphism with Mathlib's convention for multiplication in `Equiv.Perm`. -/
def permutationUnitary : Equiv.Perm n →* unitaryGroup n R :=
  (permMatrixHom (R := R)).codRestrict _ fun σ => by
    rw [permMatrixHom_apply]
    exact permMatrix_mem_unitaryGroup σ⁻¹

/-- The matrix underlying `permutationUnitary σ` is the permutation matrix of `σ⁻¹`. -/
@[simp]
theorem coe_permutationUnitary (σ : Equiv.Perm n) :
    (permutationUnitary (R := R) σ : Matrix n n R) = σ⁻¹.permMatrix R :=
  (rfl)

end Matrix
