/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Rev
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The antitranspose of a square matrix

The antitranspose of a square matrix `A` indexed by `Fin m` is its reflection in the
antidiagonal, `Aᴬ i j = A (rev j) (rev i)`; for `2 × 2` matrices it sends `(a b; c d)` to
`(d b; c a)`. Over a commutative ring it reverses products and preserves determinants, so it
is an anti-involution of the matrix ring and of the special linear group.

## Main declarations

* `Matrix.antitranspose`: the reflection of a square matrix in its antidiagonal.
* `Matrix.antitranspose_one`, `Matrix.antitranspose_add`: the antitranspose fixes `1` and is
  additive.
* `Matrix.antitranspose_mul`: the antitranspose reverses products.
* `Matrix.det_antitranspose`: the antitranspose preserves determinants.
* `Matrix.antitranspose_fin_two`: the antitranspose of `(a b; c d)` is `(d b; c a)`.
-/

public section

namespace Matrix

variable {α : Type*} {m : ℕ}

/-- The antitranspose of a square matrix: its reflection in the antidiagonal,
`A.antitranspose i j = A (rev j) (rev i)`. -/
def antitranspose (A : Matrix (Fin m) (Fin m) α) : Matrix (Fin m) (Fin m) α :=
  Aᵀ.submatrix Fin.rev Fin.rev

@[simp]
theorem antitranspose_apply (A : Matrix (Fin m) (Fin m) α) (i j : Fin m) :
    A.antitranspose i j = A j.rev i.rev :=
  (rfl)

@[simp]
theorem antitranspose_antitranspose (A : Matrix (Fin m) (Fin m) α) :
    A.antitranspose.antitranspose = A := by
  ext i j
  simp

@[simp]
theorem antitranspose_zero [Zero α] : (0 : Matrix (Fin m) (Fin m) α).antitranspose = 0 := by
  ext i j
  simp

@[simp]
theorem antitranspose_one [Zero α] [One α] :
    (1 : Matrix (Fin m) (Fin m) α).antitranspose = 1 := by
  ext i j
  simp [one_apply, eq_comm]

@[simp]
theorem antitranspose_add [Add α] (A B : Matrix (Fin m) (Fin m) α) :
    (A + B).antitranspose = A.antitranspose + B.antitranspose := by
  ext i j
  simp

@[simp]
theorem antitranspose_neg [Neg α] (A : Matrix (Fin m) (Fin m) α) :
    (-A).antitranspose = -A.antitranspose := by
  ext i j
  simp

@[simp]
theorem antitranspose_sub [Sub α] (A B : Matrix (Fin m) (Fin m) α) :
    (A - B).antitranspose = A.antitranspose - B.antitranspose := by
  ext i j
  simp

@[simp]
theorem antitranspose_smul {β : Type*} [SMul β α] (c : β) (A : Matrix (Fin m) (Fin m) α) :
    (c • A).antitranspose = c • A.antitranspose := by
  ext i j
  simp

/-- The antitranspose reverses products. -/
theorem antitranspose_mul [AddCommMonoid α] [CommMagma α] (A B : Matrix (Fin m) (Fin m) α) :
    (A * B).antitranspose = B.antitranspose * A.antitranspose := by
  change (A * B)ᵀ.submatrix Fin.rev Fin.rev = _
  rw [transpose_mul]
  exact (submatrix_mul_equiv _ _ _ Fin.revPerm _).symm

/-- The antitranspose preserves determinants. -/
@[simp]
theorem det_antitranspose {R : Type*} [CommRing R] (A : Matrix (Fin m) (Fin m) R) :
    A.antitranspose.det = A.det :=
  (det_submatrix_equiv_self Fin.revPerm Aᵀ).trans (det_transpose A)

/-- The antitranspose of `(a b; c d)` is `(d b; c a)`. -/
theorem antitranspose_fin_two (A : Matrix (Fin 2) (Fin 2) α) :
    A.antitranspose = !![A 1 1, A 0 1; A 1 0, A 0 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Matrix
