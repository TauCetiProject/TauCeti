/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The strictly lower and upper triangular parts of a matrix

For a square matrix `A` with ordered indices, `strictLowerPart A` keeps the entries `A i j` with
`j < i` and `strictUpperPart A` keeps the entries with `i < j`; all other entries are `0`. With
`D = diagonal A.diag`, `L = strictLowerPart A` and `U = strictUpperPart A`, a square matrix splits
as `A = D + L + U`. This splitting is the base of the Jacobi and the successive over-relaxation
iterations.

## Main declarations

* `Matrix.strictLowerPart A`, `Matrix.strictUpperPart A`: the strictly lower and upper triangular
  parts of `A`.
* `Matrix.isLowerTriangular_strictLowerPart`, `Matrix.isUpperTriangular_strictUpperPart`: the two
  parts are triangular.
* `Matrix.diagonal_diag_add_strictLowerPart_add_strictUpperPart`: `D + L + U = A`.
* `Matrix.isLowerTriangular_diagonal_add_smul_strictLowerPart`,
  `Matrix.isUpperTriangular_smul_diagonal_sub_smul_strictUpperPart`: `D + ω • L` is lower
  triangular and `(1 - ω) • D - ω • U` is upper triangular.
* `Matrix.diagonal_add_smul_strictLowerPart_eq`: `D + ω • L = ((1 - ω) • D - ω • U) + ω • A`.
-/

public section

namespace Matrix

variable {ι R : Type*}

section Parts

variable [Zero R] [LT ι] [DecidableLT ι]

/-- The strictly lower triangular part of a square matrix: the entries `A i j` with `j < i`, and
`0` elsewhere. -/
def strictLowerPart (A : Matrix ι ι R) : Matrix ι ι R :=
  of fun i j ↦ if j < i then A i j else 0

/-- The strictly upper triangular part of a square matrix: the entries `A i j` with `i < j`, and
`0` elsewhere. -/
def strictUpperPart (A : Matrix ι ι R) : Matrix ι ι R :=
  of fun i j ↦ if i < j then A i j else 0

/-- The entries of the strictly lower triangular part. -/
@[simp]
theorem strictLowerPart_apply (A : Matrix ι ι R) (i j : ι) :
    strictLowerPart A i j = if j < i then A i j else 0 :=
  (rfl)

/-- The entries of the strictly upper triangular part. -/
@[simp]
theorem strictUpperPart_apply (A : Matrix ι ι R) (i j : ι) :
    strictUpperPart A i j = if i < j then A i j else 0 :=
  (rfl)

end Parts

section Triangular

variable [Preorder ι] [DecidableLT ι]

/-- The strictly lower triangular part of a matrix is lower triangular. -/
theorem isLowerTriangular_strictLowerPart [Zero R] (A : Matrix ι ι R) :
    (strictLowerPart A).IsLowerTriangular := fun i j hij ↦ by
  have hij : i < j := OrderDual.toDual_lt_toDual.mp hij
  simp [hij.not_gt]

/-- The strictly upper triangular part of a matrix is upper triangular. -/
theorem isUpperTriangular_strictUpperPart [Zero R] (A : Matrix ι ι R) :
    (strictUpperPart A).IsUpperTriangular := fun i j hij ↦ by
  -- `IsUpperTriangular` unfolds to `BlockTriangular id`, so `hij : id j < id i` is `j < i`.
  have hij : j < i := hij
  simp [hij.not_gt]

variable [DecidableEq ι]

/-- `D + ω • L` is lower triangular, where `D` and `L` are the diagonal and the strictly lower
triangular parts of `A`. -/
theorem isLowerTriangular_diagonal_add_smul_strictLowerPart [Semiring R] (A : Matrix ι ι R)
    (ω : R) : (diagonal A.diag + ω • strictLowerPart A).IsLowerTriangular :=
  (blockTriangular_diagonal _).add fun _ _ h ↦ by
    rw [Matrix.smul_apply, isLowerTriangular_strictLowerPart A h, smul_zero]

/-- `(1 - ω) • D - ω • U` is upper triangular, where `D` and `U` are the diagonal and the strictly
upper triangular parts of `A`. -/
theorem isUpperTriangular_smul_diagonal_sub_smul_strictUpperPart [Ring R] (A : Matrix ι ι R)
    (ω : R) : ((1 - ω) • diagonal A.diag - ω • strictUpperPart A).IsUpperTriangular :=
  BlockTriangular.sub (fun _ _ h ↦ by simp [blockTriangular_diagonal (b := id) A.diag h])
    fun _ _ h ↦ by rw [Matrix.smul_apply, isUpperTriangular_strictUpperPart A h, smul_zero]

end Triangular

section LinearOrder

variable [LinearOrder ι]

/-- A square matrix is the sum of its diagonal part, its strictly lower triangular part and its
strictly upper triangular part. -/
theorem diagonal_diag_add_strictLowerPart_add_strictUpperPart [AddZeroClass R]
    (A : Matrix ι ι R) :
    diagonal A.diag + strictLowerPart A + strictUpperPart A = A := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [diagonal_apply_ne _ h.ne, h, h.not_gt]
  · simp
  · simp [diagonal_apply_ne _ h.ne', h, h.not_gt]

/-- The two parts of the SOR splitting differ by `ω • A`:
`D + ω • L = ((1 - ω) • D - ω • U) + ω • A`. -/
theorem diagonal_add_smul_strictLowerPart_eq [Ring R] (A : Matrix ι ι R) (ω : R) :
    diagonal A.diag + ω • strictLowerPart A =
      (1 - ω) • diagonal A.diag - ω • strictUpperPart A + ω • A := by
  calc diagonal A.diag + ω • strictLowerPart A
      = (1 - ω) • diagonal A.diag - ω • strictUpperPart A +
          ω • (diagonal A.diag + strictLowerPart A + strictUpperPart A) := by
        simp only [smul_add, sub_smul, one_smul]
        abel
    _ = _ := by rw [diagonal_diag_add_strictLowerPart_add_strictUpperPart]

end LinearOrder

end Matrix
