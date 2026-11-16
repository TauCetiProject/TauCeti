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
expands a linear map on matrices along the matrix units. `Matrix.singleNonUnitalAlgHom` bundles
the diagonal corner embedding `x ↦ Matrix.single i i x` as a nonunital algebra homomorphism.
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

/-- The diagonal corner embedding `x ↦ Matrix.single i i x` as a nonunital `R`-algebra
homomorphism into square matrices. -/
@[expose]
public def Matrix.singleNonUnitalAlgHom (R : Type*) {ι A : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Fintype ι] [DecidableEq ι] (i : ι) :
    A →ₙₐ[R] Matrix ι ι A where
  __ := Matrix.singleAddMonoidHom i i
  map_mul' x y := (Matrix.single_mul_single_same x i i i y).symm
  map_smul' r x := (Matrix.smul_single r i i x).symm

/-- `Matrix.singleNonUnitalAlgHom R i` sends `x` to the single-entry matrix
`Matrix.single i i x`. -/
@[simp]
public theorem Matrix.singleNonUnitalAlgHom_apply (R : Type*) {ι A : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Fintype ι] [DecidableEq ι] (i : ι)
    (x : A) :
    Matrix.singleNonUnitalAlgHom R i x = Matrix.single i i x :=
  rfl

/-- The underlying linear map of `Matrix.singleNonUnitalAlgHom R i` is
`Matrix.singleLinearMap R i i`. -/
@[simp]
public theorem Matrix.toLinearMap_singleNonUnitalAlgHom (R : Type*) {ι A : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Fintype ι] [DecidableEq ι] (i : ι) :
    (Matrix.singleNonUnitalAlgHom R (A := A) i : A →ₗ[R] Matrix ι ι A) =
      Matrix.singleLinearMap R i i :=
  LinearMap.ext fun _ ↦ rfl

/-- The diagonal corner embedding `Matrix.singleNonUnitalAlgHom R i` is injective. -/
public theorem Matrix.singleNonUnitalAlgHom_injective (R : Type*) {ι A : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Fintype ι] [DecidableEq ι] (i : ι) :
    Function.Injective (Matrix.singleNonUnitalAlgHom R (A := A) i) :=
  fun _ _ h ↦ by simpa using congrArg (fun M : Matrix ι ι A ↦ M i i) h
