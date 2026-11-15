/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Data.Matrix.Basis

/-!
# Products of matrix units

`Matrix.single_mul_single_eq_ite` combines the matching-index and unequal-index product
identities into one formula for rectangular matrix units with arbitrary coefficients.
Only the shared index type needs to be finite. `Matrix.single_mul_eq_sum_single` and
`Matrix.mul_single_eq_sum_single` expand left and right multiplication by a matrix unit along the
matching row or column. `Matrix.smul_vecMulVec_single_single` writes a
scaled outer product of two coordinate vectors as a matrix unit, and
`Matrix.one_add_single_mul_one_add_single_of_ne` multiplies two elementary matrices `1 + c Eᵢⱼ`
and `1 + d Eₖₗ` with `j ≠ k`, whose cross term vanishes. `Matrix.singleNonUnitalAlgHom` bundles
inclusion into a diagonal corner as a nonunital algebra homomorphism, and
`LinearMap.apply_eq_sum_sum_smul_single` expands a linear map on matrices along the matrix units.
-/

/-- The product of two matrix units vanishes unless their inner indices agree. -/
public theorem Matrix.single_mul_single_eq_ite {l m n R : Type*}
    [NonUnitalNonAssocSemiring R] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    [Fintype m] (i : l) (j k : m) (a : n) (c d : R) :
    Matrix.single i j c * Matrix.single k a d =
      if j = k then Matrix.single i a (c * d) else 0 := by
  by_cases h : j = k
  · subst k
    simp only [Matrix.single_mul_single_same, ↓reduceIte]
  · simp only [Matrix.single_mul_single_of_ne (c := c) i j k h d, h, ↓reduceIte]

/-- Left multiplication by a matrix unit expands along the matching row of the right factor. -/
public theorem Matrix.single_mul_eq_sum_single {l m n R : Type*}
    [NonUnitalNonAssocSemiring R] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    [Fintype m] [Fintype n] (i : l) (j : m) (c : R) (A : Matrix m n R) :
    Matrix.single i j c * A = ∑ k : n, Matrix.single i k (c * A j k) := by
  ext a b
  rw [Matrix.mul_apply, Matrix.sum_apply, Finset.sum_eq_single j, Finset.sum_eq_single b]
  · by_cases h : i = a <;> simp [Matrix.single, h]
  · intro k _ hk
    simp [hk]
  · intro hb
    exact (hb (Finset.mem_univ b)).elim
  · intro r _ hr
    simp [hr.symm]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Right multiplication by a matrix unit expands along the matching column of the left factor. -/
public theorem Matrix.mul_single_eq_sum_single {l m n R : Type*}
    [NonUnitalNonAssocSemiring R] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    [Fintype l] [Fintype m] (A : Matrix l m R) (j : m) (k : n) (c : R) :
    A * Matrix.single j k c = ∑ i : l, Matrix.single i k (A i j * c) := by
  ext a b
  rw [Matrix.mul_apply, Matrix.sum_apply, Finset.sum_eq_single j, Finset.sum_eq_single a]
  · by_cases h : k = b <;> simp [Matrix.single, h]
  · intro i _ hi
    simp [Matrix.single_apply_of_row_ne hi]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim
  · intro r _ hr
    simp [Matrix.single_apply_of_row_ne hr.symm]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

/-- Inclusion into a diagonal matrix corner as a nonunital algebra homomorphism. -/
public def Matrix.singleNonUnitalAlgHom (R α : Type*) {n : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring α] [DistribMulAction R α] [Fintype n] [DecidableEq n] (i : n) :
    α →ₙₐ[R] Matrix n n α where
  toFun := Matrix.single i i
  map_zero' := Matrix.single_zero i i
  map_add' := Matrix.single_add i i
  map_smul' r a := by simp
  map_mul' a b := (Matrix.single_mul_single_same a i i i b).symm

/-- `Matrix.singleNonUnitalAlgHom` places its argument in the `(i, i)` matrix entry. -/
@[simp]
public theorem Matrix.singleNonUnitalAlgHom_apply {R α n : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring α] [DistribMulAction R α] [Fintype n] [DecidableEq n]
    (i : n) (a : α) :
    Matrix.singleNonUnitalAlgHom R α i a = Matrix.single i i a :=
  (rfl)

/-- As a linear map, `Matrix.singleNonUnitalAlgHom` is `Matrix.singleLinearMap` at the diagonal
entry `(i, i)`. -/
@[simp]
public theorem Matrix.coe_singleNonUnitalAlgHom_linearMap {R α n : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring α] [Module R α] [Fintype n] [DecidableEq n] (i : n) :
    (Matrix.singleNonUnitalAlgHom R α i : α →ₗ[R] Matrix n n α) = Matrix.singleLinearMap R i i :=
  (rfl)

/-- A scaled outer product of two coordinate vectors is a matrix unit. -/
public theorem Matrix.smul_vecMulVec_single_single {m n R : Type*} [MulZeroOneClass R]
    [DecidableEq m] [DecidableEq n] (i : m) (j : n) (c : R) :
    c • Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1) = Matrix.single i j c := by
  rw [← Matrix.single_eq_single_vecMulVec_single, Matrix.smul_single, smul_eq_mul, mul_one]

/-- Two elementary matrices `1 + c Eᵢⱼ` and `1 + d Eₖₗ` multiply without a cross term when the
column `j` of the first differs from the row `k` of the second. -/
public theorem Matrix.one_add_single_mul_one_add_single_of_ne {n R : Type*}
    [NonAssocSemiring R] [DecidableEq n] [Fintype n] {i j k l : n} (h : j ≠ k) (c d : R) :
    (1 + Matrix.single i j c) * (1 + Matrix.single k l d) =
      1 + Matrix.single i j c + Matrix.single k l d := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.single_mul_single_of_ne (c := c) i j k h d, add_zero, add_right_comm]

/-- A linear map on matrices is determined by its values on the matrix units: it sends `A` to the
sum of `A i j • f (single i j 1)`. -/
public theorem LinearMap.apply_eq_sum_sum_smul_single {ι κ R M : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Semiring R] [AddCommMonoid M] [Module R M]
    (f : Matrix ι κ R →ₗ[R] M) (A : Matrix ι κ R) :
    f A = ∑ i, ∑ j, A i j • f (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
