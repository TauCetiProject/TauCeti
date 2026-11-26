/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# The trace pairing `tr (Aᵀ * B)` of matrices

The trace pairing `A : B = tr (Aᵀ * B)` is the entrywise (Frobenius) contraction
`∑ i, ∑ j, A i j * B i j` of two matrices of the same shape. This file collects its
coordinate-free properties over rings without a star structure, spelled with Mathlib's
`Matrix.trace`, transpose and multiplication.

Bilinearity is Mathlib's `Matrix.trace_add`, `Matrix.trace_smul`, `Matrix.add_mul` and
`Matrix.transpose_add`; compatibility with transposition, `tr (Aᵀ * B) = tr (A * Bᵀ)`, is
Mathlib's `Matrix.trace_transpose_mul` applied to `A` and `Bᵀ`.

## Main results

* `Matrix.trace_transpose_mul_eq_sum`: the trace pairing is the sum of entrywise products.
* `Matrix.trace_transpose_mul_comm`: the trace pairing is symmetric.
* `Matrix.IsSymm.trace_transpose_mul_eq_zero`: symmetric and skew-symmetric matrices are
  orthogonal for the trace pairing.
* `Matrix.trace_transpose_mul_self_nonneg`, `Matrix.trace_transpose_mul_self_eq_zero_iff`: over a
  strictly ordered ring the trace pairing is positive definite.
* `Matrix.trace_transpose_mul_of_transpose_mul_eq_one`: the congruence `A ↦ O A Oᵀ` by a matrix
  with orthonormal columns, in particular by an orthogonal matrix, preserves the trace pairing.
-/

public section

namespace Matrix

variable {l m n R : Type*} [Fintype m] [Fintype n]

/-- The trace pairing `tr (Aᵀ * B)` is the sum `∑ i, ∑ j, A i j * B i j` of entrywise products. -/
theorem trace_transpose_mul_eq_sum [AddCommMonoid R] [Mul R] (A B : Matrix m n R) :
    (Aᵀ * B).trace = ∑ i, ∑ j, A i j * B i j := by
  simp only [trace, diag, Matrix.mul_apply, transpose_apply]
  exact Finset.sum_comm

/-- The trace pairing is symmetric: `tr (Aᵀ * B) = tr (Bᵀ * A)`. -/
theorem trace_transpose_mul_comm [AddCommMonoid R] [CommMagma R] (A B : Matrix m n R) :
    (Aᵀ * B).trace = (Bᵀ * A).trace := by
  rw [← trace_transpose, transpose_mul, transpose_transpose]

/-- A symmetric and a skew-symmetric matrix are orthogonal for the trace pairing. -/
theorem IsSymm.trace_transpose_mul_eq_zero [CommRing R] [NoZeroDivisors R] [CharZero R]
    {A B : Matrix n n R} (hA : A.IsSymm) (hB : Bᵀ = -B) : (Aᵀ * B).trace = 0 := by
  have h : (Aᵀ * B).trace = -(Aᵀ * B).trace := by
    conv_lhs => rw [trace_transpose_mul_comm, hB, Matrix.neg_mul, trace_neg, trace_mul_comm]
    rw [hA.eq]
  rwa [eq_neg_iff_add_eq_zero, add_self_eq_zero] at h

/-- Over an ordered ring the trace pairing of a matrix with itself is nonnegative. -/
theorem trace_transpose_mul_self_nonneg [Ring R] [LinearOrder R] [IsOrderedRing R]
    (A : Matrix m n R) : 0 ≤ (Aᵀ * A).trace := by
  rw [trace_transpose_mul_eq_sum]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg (A i j)

/-- Over a strictly ordered ring the trace pairing of a matrix with itself vanishes only at
zero. -/
@[simp]
theorem trace_transpose_mul_self_eq_zero_iff [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    {A : Matrix m n R} : (Aᵀ * A).trace = 0 ↔ A = 0 := by
  rw [← vec_dotProduct_vec, dotProduct_self_eq_zero, vec_eq_zero_iff]

/-- Applying the congruence `A ↦ O A Oᵀ` to both arguments, for a matrix `O` with
orthonormal columns, `Oᵀ * O = 1`, preserves the trace pairing. This applies to every
orthogonal matrix, reflections included, through `Matrix.mem_orthogonalGroup_iff'`. -/
theorem trace_transpose_mul_of_transpose_mul_eq_one [Fintype l] [DecidableEq n] [CommSemiring R]
    {O : Matrix l n R} (hO : Oᵀ * O = 1) (A B : Matrix n n R) :
    ((O * A * Oᵀ)ᵀ * (O * B * Oᵀ)).trace = (Aᵀ * B).trace := by
  have h : (O * A * Oᵀ)ᵀ * (O * B * Oᵀ) = O * (Aᵀ * B) * Oᵀ := by
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Oᵀ O, hO, Matrix.one_mul]
  rw [h, trace_mul_cycle, ← Matrix.mul_assoc, hO, Matrix.one_mul]

end Matrix
