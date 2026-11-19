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
Only the shared index type needs to be finite. `Matrix.smul_vecMulVec_single_single` writes a
scaled outer product of two coordinate vectors as a matrix unit, and
`Matrix.one_add_single_mul_one_add_single_of_ne` multiplies two elementary matrices `1 + c Eᵢⱼ`
and `1 + d Eₖₗ` with `j ≠ k`, whose cross term vanishes. `LinearMap.apply_eq_sum_sum_smul_single`
expands a linear map on matrices along the matrix units. `Matrix.singleNonUnitalAlgHom` is the
inclusion `a ↦ a Eᵢᵢ` of the coefficients into a diagonal corner, as a homomorphism of nonunital
algebras.
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

/-- The inclusion `a ↦ a Eᵢᵢ` of the coefficients into the `(i, i)` corner of the matrix algebra,
as a homomorphism of nonunital algebras. -/
@[expose]
public def Matrix.singleNonUnitalAlgHom (R : Type*) {n α : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring α] [DistribMulAction R α] [DecidableEq n] [Fintype n] (i : n) :
    α →ₙₐ[R] Matrix n n α where
  toFun := Matrix.single i i
  map_smul' c a := (Matrix.smul_single c i i a).symm
  map_zero' := Matrix.single_zero i i
  map_add' := Matrix.single_add i i
  map_mul' a b := (Matrix.single_mul_single_same a i i i b).symm

/-- `Matrix.singleNonUnitalAlgHom R i` sends `a` to the matrix unit `Matrix.single i i a`. -/
@[simp]
public theorem Matrix.singleNonUnitalAlgHom_apply (R : Type*) {n α : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring α] [DistribMulAction R α] [DecidableEq n] [Fintype n] (i : n)
    (a : α) : Matrix.singleNonUnitalAlgHom R i a = Matrix.single i i a :=
  rfl

/-- The linear map underlying `Matrix.singleNonUnitalAlgHom R i` is `Matrix.singleLinearMap`. -/
public theorem Matrix.toLinearMap_singleNonUnitalAlgHom (R : Type*) {n α : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring α] [Module R α] [DecidableEq n] [Fintype n] (i : n) :
    ((Matrix.singleNonUnitalAlgHom R i : α →ₙₐ[R] Matrix n n α) : α →ₗ[R] Matrix n n α) =
      Matrix.singleLinearMap R i i :=
  LinearMap.ext fun _ ↦ rfl
