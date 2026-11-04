/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Matrices skew-adjoint for a bilinear form

For a square matrix `J`, Mathlib's `Matrix.IsSkewAdjoint J A` is the condition `Aᵀ * J = J * -A`:
the matrix `A` is skew-adjoint for the bilinear form `B(u, v) = u ⬝ᵥ J v`. This file records
basic facts about such matrices, independent of any Lie theory.

When `J` is invertible, skew-adjointness makes `Aᵀ` conjugate to `-A`, so `A` has trace zero as
soon as `2` is invertible. When `J` is symmetric, every pair of vectors `u`, `v` gives a
skew-adjoint matrix, the matrix `vecMulVec v (u ᵥ* J) - vecMulVec u (v ᵥ* J)` sending `x`
to `B(u, x) v - B(v, x) u`.

The file also records the matrices preserving `J` by congruence, `M * J * Mᵀ = J`: a square-zero
matrix `Y` with `Y * J + J * Yᵀ = 0`, that is, with `Yᵀ` skew-adjoint for `J`, gives the
form-preserving unipotents `1 + t • Y`; a diagonal matrix preserves `J` as soon as it does so
entrywise; when `J * J = -1`, the row and column conventions agree for matrices with a left
inverse; and a scalar matrix `c • 1` can only preserve an invertible `J` when `c ^ 2 = 1`.

## Main results

* `Matrix.isUnit_of_mul_self_eq_neg_one`: a form matrix whose square is minus the identity
  is a unit over any ring.
* `Matrix.IsSkewAdjoint.trace_eq_zero`: a matrix skew-adjoint for an invertible matrix has trace
  zero when `2` is invertible.
* `Matrix.isSkewAdjoint_vecMulVec_sub_vecMulVec`: for symmetric `J`, the matrix
  `vecMulVec v (u ᵥ* J) - vecMulVec u (v ᵥ* J)` is skew-adjoint for `J`.
* `Matrix.vecMulVec_sub_vecMulVec_mulVec`: that matrix sends `x` to
  `(u ⬝ᵥ J *ᵥ x) • v - (v ⬝ᵥ J *ᵥ x) • u`.
* `Matrix.one_add_smul_mul_mul_transpose`: a square-zero matrix `Y` with `Y * J + J * Yᵀ = 0`
  gives form-preserving unipotents.
* `Matrix.diagonal_mul_mul_transpose_diagonal`: a diagonal matrix preserving `J` entrywise
  preserves it over any semiring.
* `Matrix.transpose_mul_mul_eq_of_mul_mul_transpose_eq`: for `J * J = -1`, a matrix with a left
  inverse preserving `J` in the row convention preserves it in the column convention over any ring.
* `Matrix.sq_eq_one_of_smul_one_mul_mul_transpose_eq`: for invertible `J` over a nonempty index
  type and a commutative semiring, a scalar matrix preserving `J` has scalar of square one.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n]

/-- A matrix whose square is minus the identity is a unit, with inverse its negative. -/
theorem isUnit_of_mul_self_eq_neg_one [Ring R] [DecidableEq n] {J : Matrix n n R}
    (hJ : J * J = -1) : IsUnit J :=
  isUnit_iff_exists.2 ⟨-J, by rw [mul_neg, hJ, neg_neg], by rw [neg_mul, hJ, neg_neg]⟩

section

variable [CommRing R]

/-- **A matrix skew-adjoint for an invertible matrix has trace zero** when `2` is invertible:
skew-adjointness makes `Aᵀ` conjugate to `-A`. -/
theorem IsSkewAdjoint.trace_eq_zero [DecidableEq n] [Invertible (2 : R)] {J A : Matrix n n R}
    (hJ : IsUnit J) (hA : J.IsSkewAdjoint A) : A.trace = 0 := by
  rw [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair] at hA
  have := hJ.invertible
  have h : A.trace = -A.trace := calc
    A.trace = (Aᵀ * J * ⅟J).trace := by
      rw [Matrix.mul_assoc, mul_invOf_self, Matrix.mul_one, trace_transpose]
    _ = (J * (-A * ⅟J)).trace := by rw [hA, Matrix.mul_assoc]
    _ = -A.trace := by
      rw [trace_mul_comm, Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one, trace_neg]
  have h2 : (2 : R) * A.trace = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  rw [← invOf_mul_cancel_left (2 : R) A.trace, h2, mul_zero]

/-- For a symmetric matrix `J`, the matrix sending `x` to `(u ⬝ᵥ J x) • v - (v ⬝ᵥ J x) • u` is
skew-adjoint for `J`. -/
theorem isSkewAdjoint_vecMulVec_sub_vecMulVec {J : Matrix n n R} (hJ : J.IsSymm) (u v : n → R) :
    J.IsSkewAdjoint (vecMulVec v (u ᵥ* J) - vecMulVec u (v ᵥ* J)) := by
  have h (w : n → R) : J *ᵥ w = w ᵥ* J := by rw [← vecMul_transpose, hJ.eq]
  rw [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  simp only [transpose_sub, transpose_vecMulVec, Matrix.sub_mul, vecMulVec_mul, Matrix.mul_sub,
    mul_vecMulVec, h, neg_sub]

/-- The matrix `vecMulVec v (u ᵥ* J) - vecMulVec u (v ᵥ* J)` sends `x` to
`(u ⬝ᵥ J *ᵥ x) • v - (v ⬝ᵥ J *ᵥ x) • u`. -/
theorem vecMulVec_sub_vecMulVec_mulVec (J : Matrix n n R) (u v x : n → R) :
    (vecMulVec v (u ᵥ* J) - vecMulVec u (v ᵥ* J)) *ᵥ x =
      (u ⬝ᵥ J *ᵥ x) • v - (v ⬝ᵥ J *ᵥ x) • u := by
  simp [sub_mulVec, vecMulVec_mulVec, dotProduct_mulVec]

/-! ### Matrices preserving a form -/

variable [DecidableEq n]

/-- **A square-zero matrix `Y` with `Y * J + J * Yᵀ = 0` gives form-preserving unipotents**:
`(1 + t • Y) * J * (1 + t • Y)ᵀ = J` for every scalar `t`. -/
theorem one_add_smul_mul_mul_transpose (J Y : Matrix n n R) (t : R)
    (hskew : Y * J + J * Yᵀ = 0) (hsq : Y * Y = 0) :
    (1 + t • Y) * J * (1 + t • Y)ᵀ = J := by
  have hYJ : Y * J = -(J * Yᵀ) := eq_neg_iff_add_eq_zero.mpr hskew
  have hcube : Y * J * Yᵀ = 0 := by
    rw [hYJ, neg_mul, mul_assoc, ← transpose_mul, hsq, transpose_zero, mul_zero, neg_zero]
  simp only [transpose_add, transpose_one, transpose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one, smul_mul, Matrix.mul_smul]
  rw [hcube, smul_zero, add_zero, hYJ, smul_neg]
  abel

end

variable [DecidableEq n]

/-- Over any semiring, a diagonal matrix preserves a form `J` as soon as it does so entrywise:
`d i * J i j * d j = J i j` for all `i` and `j`. -/
theorem diagonal_mul_mul_transpose_diagonal [Semiring R] (d : n → R) (J : Matrix n n R)
    (hd : ∀ i j, d i * J i j * d j = J i j) :
    diagonal d * J * (diagonal d)ᵀ = J := by
  ext i j
  rw [diagonal_transpose, mul_diagonal, diagonal_mul]
  exact hd i j

/-- **For a form `J` with `J * J = -1`, the row and column conventions agree**: a matrix `M` with
a left inverse and `M * J * Mᵀ = J` satisfies `Mᵀ * J * M = J`, over any ring. -/
theorem transpose_mul_mul_eq_of_mul_mul_transpose_eq [Ring R] {J M N : Matrix n n R}
    (hJ : J * J = -1) (hNM : N * M = 1) (h : M * J * Mᵀ = J) : Mᵀ * J * M = J := by
  have hleft : J * Mᵀ = N * J := by
    calc J * Mᵀ = N * M * J * Mᵀ := by rw [hNM, Matrix.one_mul]
      _ = N * (M * J * Mᵀ) := by simp only [Matrix.mul_assoc]
      _ = N * J := by rw [h]
  calc Mᵀ * J * M = -(J * J) * Mᵀ * J * M := by rw [hJ, neg_neg, Matrix.one_mul]
    _ = -(J * (J * Mᵀ) * J * M) := by simp only [Matrix.neg_mul, Matrix.mul_assoc]
    _ = -(J * (N * J) * J * M) := by rw [hleft]
    _ = -(J * N * (J * J) * M) := by simp only [Matrix.mul_assoc]
    _ = J * N * M := by rw [hJ, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, neg_neg]
    _ = J := by rw [Matrix.mul_assoc, hNM, Matrix.mul_one]

/-- **A scalar matrix preserving an invertible form `J` has scalar of square one**, over a
nonempty index type and a commutative semiring. -/
theorem sq_eq_one_of_smul_one_mul_mul_transpose_eq [CommSemiring R] [Nonempty n] {J : Matrix n n R}
    (hJ : IsUnit J) {c : R} (h : (c • 1) * J * (c • 1)ᵀ = J) : c ^ 2 = 1 := by
  have hJ' : c ^ 2 • J = J := by
    simpa only [transpose_smul, transpose_one, smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one, smul_smul, pow_two] using h
  have := hJ.invertible
  have h1 : c ^ 2 • (1 : Matrix n n R) = 1 := by
    rw [← mul_invOf_self J, ← Matrix.smul_mul, hJ']
  have h2 := congrFun (congrFun h1 (Classical.arbitrary n)) (Classical.arbitrary n)
  simpa only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] using h2

end Matrix
