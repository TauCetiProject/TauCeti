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
expands a linear map on matrices along the matrix units, and `TauCeti.matrixCornerNonUnitalAlgHom`
bundles the `(r, r)` diagonal corner inclusion as a nonunital algebra homomorphism.
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

/-- The `(r, r)` diagonal corner inclusion `x ↦ Matrix.single r r x` as `A →ₙₐ[R] Matrix ι ι A`. -/
public def TauCeti.matrixCornerNonUnitalAlgHom (R A : Type*) {ι : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Fintype ι] [DecidableEq ι] (r : ι) :
    A →ₙₐ[R] Matrix ι ι A where
  __ := Matrix.singleLinearMap R r r
  map_zero' := map_zero (Matrix.singleLinearMap R r r)
  map_mul' x y := (Matrix.single_mul_single_same x r r r y).symm

/-- Evaluating `matrixCornerNonUnitalAlgHom` gives `Matrix.single r r`. -/
@[simp]
public theorem TauCeti.matrixCornerNonUnitalAlgHom_apply {R A ι : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Fintype ι] [DecidableEq ι] (r : ι) (x : A) :
    TauCeti.matrixCornerNonUnitalAlgHom R A r x = Matrix.single r r x :=
  Matrix.singleLinearMap_apply R r r x

/-- The underlying linear map of `matrixCornerNonUnitalAlgHom` is `Matrix.singleLinearMap`. -/
@[simp]
public theorem TauCeti.toLinearMap_matrixCornerNonUnitalAlgHom (R A : Type*) {ι : Type*}
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Fintype ι] [DecidableEq ι] (r : ι) :
    (TauCeti.matrixCornerNonUnitalAlgHom R A r : A →ₗ[R] Matrix ι ι A) =
      Matrix.singleLinearMap R r r := by ext; simp
