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
expands a linear map on matrices along the matrix units. `Matrix.sum_mul_single_eq_mul_mul_single`,
`Matrix.sum_single_eq_mul_single`, and `Matrix.sum_single_eq_single_mul` contract sums of matrix
units weighted by a column or row of a matrix into a single matrix product.
`Matrix.singleNonUnitalAlgHom` packages the `(r, r)` diagonal corner embedding as a homomorphism of
nonunital algebras.
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

/-- Summing `a * Matrix.single t r (b t s)` over `t` computes `(a * b) * Matrix.single s r 1`. -/
public theorem Matrix.sum_mul_single_eq_mul_mul_single {l m n p R : Type*} [NonAssocSemiring R]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (r : p) (s : n) (a : Matrix l m R) (b : Matrix m n R) :
    ∑ t : m, a * Matrix.single t r (b t s) = (a * b) * Matrix.single s r (1 : R) := by
  ext u v
  rw [Matrix.sum_apply]
  by_cases hv : v = r
  · subst hv
    simp only [Matrix.mul_single_apply_same, mul_one]
    rw [Matrix.mul_apply]
  · simp [Matrix.mul_single_apply_of_ne (hbj := hv)]

/-- Summing `Matrix.single t r (a t s)` over `t` computes `a * Matrix.single s r 1`. -/
public theorem Matrix.sum_single_eq_mul_single {l m n R : Type*} [NonAssocSemiring R]
    [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    (r : n) (s : m) (a : Matrix l m R) :
    ∑ t : l, Matrix.single t r (a t s) = a * Matrix.single s r (1 : R) := by
  ext u v
  rw [Matrix.sum_apply]
  by_cases hv : v = r
  · subst hv
    simp [Matrix.mul_single_apply_same, Matrix.single_apply]
  · simp [Matrix.mul_single_apply_of_ne (hbj := hv), Ne.symm hv]

/-- Summing `Matrix.single r t (a s t)` over `t` computes `Matrix.single r s 1 * a`. -/
public theorem Matrix.sum_single_eq_single_mul {l m n R : Type*} [NonAssocSemiring R]
    [Fintype m] [Fintype n] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    (r : l) (s : m) (a : Matrix m n R) :
    ∑ t : n, Matrix.single r t (a s t) = Matrix.single r s (1 : R) * a := by
  ext u v
  rw [Matrix.sum_apply]
  by_cases hu : u = r
  · subst hu
    simp [Matrix.single_mul_apply_same, Matrix.single_apply]
  · simp [Matrix.single_mul_apply_of_ne (h := hu), Ne.symm hu]

/-- Embedding `A` into the `(r, r)` diagonal corner of `Matrix ι ι A` as a homomorphism of
nonunital algebras. -/
public def Matrix.singleNonUnitalAlgHom (R : Type*) {ι A : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Fintype ι] [DecidableEq ι]
    (r : ι) : A →ₙₐ[R] Matrix ι ι A where
  toFun := Matrix.single r r
  map_zero' := Matrix.single_zero r r
  map_add' := Matrix.single_add r r
  map_smul' c a := (Matrix.smul_single c r r a).symm
  map_mul' a b := (Matrix.single_mul_single_same a r r r b).symm

/-- The diagonal corner embedding `Matrix.singleNonUnitalAlgHom` sends `a` to
`Matrix.single r r a`. -/
@[simp]
public theorem Matrix.singleNonUnitalAlgHom_apply (R : Type*) {ι A : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Fintype ι] [DecidableEq ι]
    (r : ι) (a : A) :
    Matrix.singleNonUnitalAlgHom R r a = Matrix.single r r a := by
  rfl

/-- As a linear map, `Matrix.singleNonUnitalAlgHom` is `Matrix.singleLinearMap R r r`. -/
@[simp]
public theorem Matrix.coe_singleNonUnitalAlgHom_eq_singleLinearMap (R : Type*) {ι A : Type*}
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Fintype ι] [DecidableEq ι] (r : ι) :
    ((Matrix.singleNonUnitalAlgHom R (A := A) r : A →ₙₐ[R] Matrix ι ι A) : A →ₗ[R] Matrix ι ι A) =
      Matrix.singleLinearMap R r r := by
  ext a
  rfl
