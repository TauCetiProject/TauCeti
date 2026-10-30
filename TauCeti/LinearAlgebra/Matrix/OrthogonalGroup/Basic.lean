/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Scalar, diagonal and determinant facts for orthogonal matrices

A scalar matrix `c • 1` over a nonempty index type lies in the orthogonal group of the standard
symmetric form only when `c ^ 2 = 1`. For an empty index type every scalar qualifies.

Over a ring without zero divisors an orthogonal matrix has determinant `1` or `-1`, and both values
occur as soon as the index type is nonempty: the diagonal reflection negating one coordinate is an
orthogonal matrix of determinant `-1`.

## Main definitions

* `TauCeti.orthogonalDiagonalReflection`: the diagonal orthogonal matrix negating one coordinate.

## Main declarations

* `TauCeti.sq_eq_one_of_smul_one_mem_orthogonalGroup`: a scalar orthogonal matrix over a nonempty
  index type has scalar a square root of one.
* `TauCeti.det_eq_one_or_neg_one_of_mem_orthogonalGroup`: the determinant of an orthogonal matrix
  is `1` or `-1`.
* `TauCeti.det_orthogonalDiagonalReflection`: the diagonal reflection has determinant `-1`.
-/

public section

namespace TauCeti

/-- A scalar matrix preserving the standard symmetric form has scalar a square root of one,
provided the index type is nonempty: the orthogonality relation reads `c ^ 2 • 1 = 1`. -/
theorem sq_eq_one_of_smul_one_mem_orthogonalGroup {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {R : Type*} [CommRing R] {c : R}
    (h : c • (1 : Matrix n n R) ∈ Matrix.orthogonalGroup n R) : c ^ 2 = 1 := by
  rw [Matrix.mem_orthogonalGroup_iff] at h
  have hentry := congrFun (congrFun h (Classical.arbitrary n)) (Classical.arbitrary n)
  simpa [sq] using hentry

/-- Over a ring without zero divisors, the determinant of an orthogonal matrix is `1` or `-1`: the
orthogonality relation `Aᵀ * A = 1` gives `det A * det A = 1`. -/
theorem det_eq_one_or_neg_one_of_mem_orthogonalGroup {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] [NoZeroDivisors R] {A : Matrix n n R}
    (hA : A ∈ Matrix.orthogonalGroup n R) : A.det = 1 ∨ A.det = -1 := by
  have h := congrArg Matrix.det ((Matrix.mem_orthogonalGroup_iff n R).1 hA)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  exact mul_self_eq_one_iff.1 h

section DiagonalReflection

variable {n : Type*} [Fintype n] [DecidableEq n] (R : Type*) [CommRing R]

/-- The diagonal reflection negating the coordinate `i`: the diagonal matrix with entry `-1` at
`i` and `1` elsewhere, an orthogonal matrix of determinant `-1`
(`TauCeti.det_orthogonalDiagonalReflection`). -/
def orthogonalDiagonalReflection (i : n) : Matrix.orthogonalGroup n R :=
  ⟨Matrix.diagonal (Function.update 1 i (-1)), by
    rw [Matrix.mem_orthogonalGroup_iff, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext j
    by_cases hj : j = i <;> simp [hj]⟩

/-- The diagonal reflection negating the coordinate `i` has underlying matrix the diagonal matrix
with entry `-1` at `i` and `1` elsewhere. -/
@[simp]
theorem coe_orthogonalDiagonalReflection (i : n) :
    (orthogonalDiagonalReflection R i : Matrix n n R) =
      Matrix.diagonal (Function.update 1 i (-1)) :=
  (rfl)

/-- The diagonal reflection negating one coordinate has determinant `-1`. -/
theorem det_orthogonalDiagonalReflection (i : n) :
    (orthogonalDiagonalReflection R i : Matrix n n R).det = -1 := by
  rw [coe_orthogonalDiagonalReflection, Matrix.det_diagonal,
    Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp

end DiagonalReflection

end TauCeti
