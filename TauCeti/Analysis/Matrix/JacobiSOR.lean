/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import TauCeti.Analysis.Matrix.StationaryIteration

/-!
# The Jacobi and the successive over-relaxation iterations

Write a square matrix `A` as `A = D + L + U`, with `D = diagonal A.diag` its diagonal part, `L`
its strictly lower triangular part and `U` its strictly upper triangular part. The classical
iterative methods for the linear system `A *ᵥ x = b` are stationary iterations
`x (k + 1) = G *ᵥ x k + c` (see `Matrix.stationaryIterate`) for the following iteration matrices:

* the Jacobi iteration, with `G = 1 - D⁻¹ * A` and `c = D⁻¹ *ᵥ b`;
* the successive over-relaxation (SOR) iteration with relaxation parameter `ω`, with
  `G = (D + ω • L)⁻¹ * ((1 - ω) • D - ω • U)` and `c = ω • ((D + ω • L)⁻¹ *ᵥ b)`. The value
  `ω = 1` gives the Gauss–Seidel iteration.

This file defines these iteration matrices and iterates over a commutative ring, and proves the
basic algebraic facts: when the diagonal entries of `A` are units, `D + ω • L` is invertible for
every `ω`, the SOR matrix has determinant `(1 - ω) ^ n`, and the fixed points of the Jacobi map,
and of the SOR map for `ω` a non-zero-divisor, are exactly the solutions of `A *ᵥ x = b`. Over a
field, the hypotheses are that the diagonal entries are nonzero and that `ω ≠ 0`.

Matrix inverses are Mathlib's `Matrix.inv`, which is `0` for a singular matrix, so the results
that need an inverse assume that the diagonal entries of `A` are units.

## Main declarations

* `Matrix.strictLowerPart A`, `Matrix.strictUpperPart A`: the strictly lower and upper triangular
  parts of `A`.
* `Matrix.diagonal_diag_add_strictLowerPart_add_strictUpperPart`: `D + L + U = A`.
* `Matrix.jacobiMatrix A`, `Matrix.jacobiIterate A b x₀`: the Jacobi iteration matrix and the
  Jacobi iterates.
* `Matrix.jacobiMatrix_apply`: the entries `1 i j - (A i i)⁻¹ * A i j` of `jacobiMatrix A`.
* `Matrix.isFixedPt_jacobiMatrix_iff`: the fixed points of the Jacobi map are the solutions of
  `A *ᵥ x = b`.
* `Matrix.sorMatrix A ω`, `Matrix.sorIterate A ω b x₀`: the SOR iteration matrix and the SOR
  iterates.
* `Matrix.det_diagonal_add_smul_strictLowerPart`: `det (D + ω • L) = ∏ i, A i i`.
* `Matrix.isUnit_diagonal_add_smul_strictLowerPart_iff`: `D + ω • L` is invertible if and only if
  the diagonal entries of `A` are units.
* `Matrix.det_sorMatrix`: `det (sorMatrix A ω) = (1 - ω) ^ n`.
* `Matrix.isFixedPt_sorMatrix_iff`: the fixed points of the SOR map are the solutions of
  `A *ᵥ x = b`.

## References

* Yousef Saad, *Iterative Methods for Sparse Linear Systems*, second edition, SIAM, 2003:
  the iterations (4.5), (4.8) and (4.12), pp. 106–107, with `E = -L` and `F = -U`.
-/

public section

open Finset

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

variable [Preorder ι] [DecidableLT ι] [DecidableEq ι] [Ring R]

/-- `D + ω • L` is lower triangular, where `D` and `L` are the diagonal and the strictly lower
triangular parts of `A`. -/
theorem isLowerTriangular_diagonal_add_smul_strictLowerPart (A : Matrix ι ι R) (ω : R) :
    (diagonal A.diag + ω • strictLowerPart A).IsLowerTriangular := fun i j hij ↦ by
  have hij : i < j := OrderDual.toDual_lt_toDual.mp hij
  simp [diagonal_apply_ne _ hij.ne, hij.not_gt]

/-- `(1 - ω) • D - ω • U` is upper triangular, where `D` and `U` are the diagonal and the strictly
upper triangular parts of `A`. -/
theorem isUpperTriangular_smul_diagonal_sub_smul_strictUpperPart (A : Matrix ι ι R) (ω : R) :
    ((1 - ω) • diagonal A.diag - ω • strictUpperPart A).IsUpperTriangular := fun i j hij ↦ by
  have hij : j < i := hij
  simp [diagonal_apply_ne _ hij.ne', hij.not_gt]

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

variable [Ring R]

/-- The two parts of the SOR splitting differ by `ω • A`:
`D + ω • L = ((1 - ω) • D - ω • U) + ω • A`. -/
theorem diagonal_add_smul_strictLowerPart_eq (A : Matrix ι ι R) (ω : R) :
    diagonal A.diag + ω • strictLowerPart A =
      (1 - ω) • diagonal A.diag - ω • strictUpperPart A + ω • A := by
  calc diagonal A.diag + ω • strictLowerPart A
      = (1 - ω) • diagonal A.diag - ω • strictUpperPart A +
          ω • (diagonal A.diag + strictLowerPart A + strictUpperPart A) := by
        simp only [smul_add, sub_smul, one_smul]
        abel
    _ = _ := by rw [diagonal_diag_add_strictLowerPart_add_strictUpperPart]

end LinearOrder

variable [Fintype ι] [CommRing R]

section Jacobi

variable [DecidableEq ι]

/-- The Jacobi iteration matrix `1 - D⁻¹ * A` of a square matrix `A`, where `D = diagonal A.diag`
is the diagonal part of `A`. -/
noncomputable def jacobiMatrix (A : Matrix ι ι R) : Matrix ι ι R :=
  1 - (diagonal A.diag)⁻¹ * A

/-- The Jacobi iterates for the linear system `A *ᵥ x = b` from `x₀`: the stationary iterates of
`x ↦ jacobiMatrix A *ᵥ x + D⁻¹ *ᵥ b`, where `D = diagonal A.diag`. -/
noncomputable def jacobiIterate (A : Matrix ι ι R) (b x₀ : ι → R) : ℕ → ι → R :=
  stationaryIterate (jacobiMatrix A) ((diagonal A.diag)⁻¹ *ᵥ b) x₀

/-- The definition of `jacobiMatrix`. -/
theorem jacobiMatrix_def (A : Matrix ι ι R) : jacobiMatrix A = 1 - (diagonal A.diag)⁻¹ * A :=
  (rfl)

/-- The Jacobi iterates are the stationary iterates of the Jacobi map. -/
theorem jacobiIterate_def (A : Matrix ι ι R) (b x₀ : ι → R) :
    jacobiIterate A b x₀ = stationaryIterate (jacobiMatrix A) ((diagonal A.diag)⁻¹ *ᵥ b) x₀ :=
  (rfl)

/-- The Jacobi iteration starts at `x₀`. -/
@[simp]
theorem jacobiIterate_zero (A : Matrix ι ι R) (b x₀ : ι → R) : jacobiIterate A b x₀ 0 = x₀ :=
  stationaryIterate_zero _ _ _

/-- One step of the Jacobi iteration. -/
@[simp]
theorem jacobiIterate_succ (A : Matrix ι ι R) (b x₀ : ι → R) (k : ℕ) :
    jacobiIterate A b x₀ (k + 1) =
      jacobiMatrix A *ᵥ jacobiIterate A b x₀ k + (diagonal A.diag)⁻¹ *ᵥ b :=
  stationaryIterate_succ _ _ _ _

private theorem isUnit_det_diagonal_diag {A : Matrix ι ι R} (hA : ∀ i, IsUnit (A i i)) :
    IsUnit (diagonal A.diag).det := by
  rw [det_diagonal, IsUnit.prod_univ_iff]
  exact hA

/-- The entries of the Jacobi iteration matrix, when the diagonal entries of `A` are units:
`jacobiMatrix A i j = 1 i j - (A i i)⁻¹ * A i j`. In particular its diagonal entries are `0`. -/
theorem jacobiMatrix_apply {A : Matrix ι ι R} (hA : ∀ i, IsUnit (A i i)) (i j : ι) :
    jacobiMatrix A i j = (1 : Matrix ι ι R) i j - Ring.inverse (A i i) * A i j := by
  have h : diagonal A.diag * ((diagonal A.diag)⁻¹ * A) = A := by
    rw [← Matrix.mul_assoc, mul_nonsing_inv _ (isUnit_det_diagonal_diag hA), Matrix.one_mul]
  have hij := congrFun₂ h i j
  rw [diagonal_mul, diag_apply] at hij
  rw [jacobiMatrix, Matrix.sub_apply, ← hij, Ring.inverse_mul_cancel_left _ _ (hA i)]

/-- The Jacobi splitting: `D * jacobiMatrix A = D - A`, where `D = diagonal A.diag`, when the
diagonal entries of `A` are units. -/
theorem diagonal_diag_mul_jacobiMatrix {A : Matrix ι ι R} (hA : ∀ i, IsUnit (A i i)) :
    diagonal A.diag * jacobiMatrix A = diagonal A.diag - A := by
  rw [jacobiMatrix, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
    mul_nonsing_inv _ (isUnit_det_diagonal_diag hA), Matrix.one_mul]

/-- If the diagonal entries of `A` are units, the fixed points of the Jacobi map
`x ↦ jacobiMatrix A *ᵥ x + D⁻¹ *ᵥ b` are exactly the solutions of `A *ᵥ x = b`. -/
theorem isFixedPt_jacobiMatrix_iff {A : Matrix ι ι R} (hA : ∀ i, IsUnit (A i i))
    (b x : ι → R) :
    Function.IsFixedPt (jacobiMatrix A *ᵥ · + (diagonal A.diag)⁻¹ *ᵥ b) x ↔ A *ᵥ x = b := by
  have hD := isUnit_det_diagonal_diag hA
  rw [Function.IsFixedPt, ← (mulVec_injective_of_isUnit
    ((isUnit_iff_isUnit_det _).mpr hD)).eq_iff, mulVec_add, mulVec_mulVec, mulVec_mulVec,
    diagonal_diag_mul_jacobiMatrix hA, mul_nonsing_inv _ hD, one_mulVec, sub_mulVec,
    sub_add_eq_add_sub, sub_eq_iff_eq_add, add_right_inj, eq_comm]

end Jacobi

section SOR

variable [LinearOrder ι]

/-- The determinant of `D + ω • L` is the product of the diagonal entries of `A`, where `D` and
`L` are the diagonal and the strictly lower triangular parts of `A`. -/
theorem det_diagonal_add_smul_strictLowerPart (A : Matrix ι ι R) (ω : R) :
    (diagonal A.diag + ω • strictLowerPart A).det = ∏ i, A i i := by
  rw [det_of_isLowerTriangular _ (isLowerTriangular_diagonal_add_smul_strictLowerPart A ω)]
  simp

/-- `D + ω • L` is invertible if and only if the diagonal entries of `A` are units, where `D` and
`L` are the diagonal and the strictly lower triangular parts of `A`. -/
theorem isUnit_diagonal_add_smul_strictLowerPart_iff {A : Matrix ι ι R} {ω : R} :
    IsUnit (diagonal A.diag + ω • strictLowerPart A) ↔ ∀ i, IsUnit (A i i) := by
  rw [isUnit_iff_isUnit_det, det_diagonal_add_smul_strictLowerPart, IsUnit.prod_univ_iff]

/-- The SOR iteration matrix `(D + ω • L)⁻¹ * ((1 - ω) • D - ω • U)` of a square matrix `A` with
relaxation parameter `ω`, where `D`, `L` and `U` are the diagonal, the strictly lower and the
strictly upper triangular parts of `A`. The value `ω = 1` gives the Gauss–Seidel matrix. -/
noncomputable def sorMatrix (A : Matrix ι ι R) (ω : R) : Matrix ι ι R :=
  (diagonal A.diag + ω • strictLowerPart A)⁻¹ *
    ((1 - ω) • diagonal A.diag - ω • strictUpperPart A)

/-- The SOR iterates for the linear system `A *ᵥ x = b` with relaxation parameter `ω` from `x₀`:
the stationary iterates of `x ↦ sorMatrix A ω *ᵥ x + ω • ((D + ω • L)⁻¹ *ᵥ b)`. When `D + ω • L`
is invertible, the step solves `(D + ω • L) *ᵥ x (k + 1) = ((1 - ω) • D - ω • U) *ᵥ x k + ω • b`
for `x (k + 1)`. -/
noncomputable def sorIterate (A : Matrix ι ι R) (ω : R) (b x₀ : ι → R) : ℕ → ι → R :=
  stationaryIterate (sorMatrix A ω) (ω • ((diagonal A.diag + ω • strictLowerPart A)⁻¹ *ᵥ b)) x₀

/-- The definition of `sorMatrix`. -/
theorem sorMatrix_def (A : Matrix ι ι R) (ω : R) :
    sorMatrix A ω = (diagonal A.diag + ω • strictLowerPart A)⁻¹ *
      ((1 - ω) • diagonal A.diag - ω • strictUpperPart A) :=
  (rfl)

/-- The SOR iterates are the stationary iterates of the SOR map. -/
theorem sorIterate_def (A : Matrix ι ι R) (ω : R) (b x₀ : ι → R) :
    sorIterate A ω b x₀ = stationaryIterate (sorMatrix A ω)
      (ω • ((diagonal A.diag + ω • strictLowerPart A)⁻¹ *ᵥ b)) x₀ :=
  (rfl)

/-- The SOR iteration starts at `x₀`. -/
@[simp]
theorem sorIterate_zero (A : Matrix ι ι R) (ω : R) (b x₀ : ι → R) :
    sorIterate A ω b x₀ 0 = x₀ :=
  stationaryIterate_zero _ _ _

/-- One step of the SOR iteration. -/
@[simp]
theorem sorIterate_succ (A : Matrix ι ι R) (ω : R) (b x₀ : ι → R) (k : ℕ) :
    sorIterate A ω b x₀ (k + 1) = sorMatrix A ω *ᵥ sorIterate A ω b x₀ k +
      ω • ((diagonal A.diag + ω • strictLowerPart A)⁻¹ *ᵥ b) :=
  stationaryIterate_succ _ _ _ _

/-- The SOR splitting: `(D + ω • L) * sorMatrix A ω = (1 - ω) • D - ω • U` when the diagonal
entries of `A` are units. -/
theorem diagonal_add_smul_strictLowerPart_mul_sorMatrix {A : Matrix ι ι R}
    (hA : ∀ i, IsUnit (A i i)) (ω : R) :
    (diagonal A.diag + ω • strictLowerPart A) * sorMatrix A ω =
      (1 - ω) • diagonal A.diag - ω • strictUpperPart A := by
  rw [sorMatrix, ← Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp
    (isUnit_diagonal_add_smul_strictLowerPart_iff.mpr hA)), Matrix.one_mul]

/-- If the diagonal entries of `A` are units, the SOR matrix has determinant `(1 - ω) ^ n`, where
`n` is the size of `A`. -/
theorem det_sorMatrix {A : Matrix ι ι R} (hA : ∀ i, IsUnit (A i i)) (ω : R) :
    (sorMatrix A ω).det = (1 - ω) ^ Fintype.card ι := by
  have hu : IsUnit (∏ i, A i i) := IsUnit.prod_univ_iff.mpr hA
  rw [sorMatrix, det_mul, det_nonsing_inv, det_diagonal_add_smul_strictLowerPart,
    det_of_isUpperTriangular (isUpperTriangular_smul_diagonal_sub_smul_strictUpperPart A ω)]
  have hN : ∏ i, ((1 - ω) • diagonal A.diag - ω • strictUpperPart A) i i =
      (1 - ω) ^ Fintype.card ι * ∏ i, A i i := by
    simp [prod_mul_distrib]
  rw [hN, mul_left_comm, Ring.inverse_mul_cancel _ hu, mul_one]

/-- With relaxation parameter `ω = 0` the SOR matrix is the identity, when the diagonal entries of
`A` are units. Then the SOR map leaves every vector fixed. -/
theorem sorMatrix_zero {A : Matrix ι ι R} (hA : ∀ i, IsUnit (A i i)) : sorMatrix A 0 = 1 := by
  rw [sorMatrix]
  simpa using nonsing_inv_mul _ (isUnit_det_diagonal_diag hA)

/-- If the diagonal entries of `A` are units and `ω` is a non-zero-divisor, the fixed points of
the SOR map `x ↦ sorMatrix A ω *ᵥ x + ω • ((D + ω • L)⁻¹ *ᵥ b)` are exactly the solutions of
`A *ᵥ x = b`. -/
theorem isFixedPt_sorMatrix_iff {A : Matrix ι ι R} (hA : ∀ i, IsUnit (A i i)) {ω : R}
    (hω : ω ∈ nonZeroDivisors R) (b x : ι → R) :
    Function.IsFixedPt
        (sorMatrix A ω *ᵥ · + ω • ((diagonal A.diag + ω • strictLowerPart A)⁻¹ *ᵥ b)) x ↔
      A *ᵥ x = b := by
  have hM : IsUnit (diagonal A.diag + ω • strictLowerPart A) :=
    isUnit_diagonal_add_smul_strictLowerPart_iff.mpr hA
  have hω' : Function.Injective (ω • · : (ι → R) → ι → R) := fun u v h ↦
    funext fun i ↦ (mul_cancel_left_mem_nonZeroDivisors hω).mp (by simpa using congrFun h i)
  rw [Function.IsFixedPt, ← (mulVec_injective_of_isUnit hM).eq_iff, mulVec_add, mulVec_mulVec,
    diagonal_add_smul_strictLowerPart_mul_sorMatrix hA, mulVec_smul, mulVec_mulVec,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hM), one_mulVec,
    diagonal_add_smul_strictLowerPart_eq, add_mulVec, smul_mulVec, add_right_inj, hω'.eq_iff,
    eq_comm]

end SOR

end Matrix
