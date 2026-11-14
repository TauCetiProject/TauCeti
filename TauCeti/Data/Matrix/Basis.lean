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
expands a linear map on matrices along the matrix units.

`Matrix.singleNonUnitalAlgHom` bundles the diagonal corner embedding `x ↦ Matrix.single r r x` as a
nonunital algebra homomorphism, accompanied by column, row, and corner-entry decomposition
identities (`Matrix.sum_single_eq_mul_single_one`, `Matrix.mul_mul_single_one`,
`Matrix.sum_mul_single_one_mul_single_one`, `Matrix.sum_mul_single_one_mul_single`,
`Matrix.sum_single_mul_single_one`, `Matrix.single_one_mul_mul_single_one`, and
`Matrix.sum_single_mul_single`) valid without associativity.
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

/-- The diagonal corner embedding `x ↦ Matrix.single r r x` as a nonunital algebra homomorphism. -/
public def Matrix.singleNonUnitalAlgHom (R : Type*) {n A : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Fintype n] [DecidableEq n] (r : n) :
    A →ₙₐ[R] Matrix n n A where
  toFun := Matrix.single r r
  map_add' := Matrix.single_add r r
  map_zero' := Matrix.single_zero r r
  map_smul' c x := (Matrix.smul_single c r r x).symm
  map_mul' x y := (Matrix.single_mul_single_same x r r r y).symm

/-- Evaluating `Matrix.singleNonUnitalAlgHom` places its input in the `(r, r)` entry. -/
@[simp]
public theorem Matrix.singleNonUnitalAlgHom_apply (R : Type*) {n A : Type*} [Monoid R]
    [NonUnitalNonAssocSemiring A] [DistribMulAction R A] [Fintype n] [DecidableEq n]
    (r : n) (x : A) :
    Matrix.singleNonUnitalAlgHom R r x = Matrix.single r r x :=
  (rfl)

/-- The underlying `R`-linear map of `Matrix.singleNonUnitalAlgHom` is
`Matrix.singleLinearMap R r r`. -/
@[simp]
public theorem Matrix.singleNonUnitalAlgHom_toLinearMap (R : Type*) {n A : Type*} [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Fintype n] [DecidableEq n] (r : n) :
    (Matrix.singleNonUnitalAlgHom R (A := A) r : A →ₗ[R] Matrix n n A) =
      Matrix.singleLinearMap R r r :=
  (rfl)

/-- Placing column `j` of `X` into column `r` as a sum of matrix units equals right multiplication
by `Matrix.single j r 1`. -/
public theorem Matrix.sum_single_eq_mul_single_one {l m n A : Type*} [NonAssocSemiring A]
    [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    (X : Matrix l m A) (j : m) (r : n) :
    ∑ u : l, Matrix.single u r (X u j) = X * Matrix.single j r (1 : A) := by
  ext u v
  rcases eq_or_ne v r with rfl | hvr
  · rw [Matrix.mul_single_apply_same, mul_one]
    simp [Matrix.single]
  · rw [Matrix.mul_single_apply_of_ne (1 : A) j r u v hvr]
    simp [Matrix.single, Ne.symm hvr]

/-- Right multiplication by a unit matrix unit `Matrix.single j r 1` associates with matrix
multiplication even when the coefficient semiring is nonassociative. -/
public theorem Matrix.mul_mul_single_one {l m n o A : Type*} [NonAssocSemiring A]
    [Fintype m] [Fintype n] [DecidableEq n] [DecidableEq o]
    (X : Matrix l m A) (Y : Matrix m n A) (j : n) (r : o) :
    X * (Y * Matrix.single j r (1 : A)) = (X * Y) * Matrix.single j r (1 : A) := by
  ext u v
  rcases eq_or_ne v r with rfl | hvr
  · rw [Matrix.mul_single_apply_same, mul_one, Matrix.mul_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun w _ ↦ by rw [Matrix.mul_single_apply_same, mul_one]
  · rw [Matrix.mul_single_apply_of_ne (1 : A) j r u v hvr, Matrix.mul_apply]
    exact Finset.sum_eq_zero fun w _ ↦ by
      rw [Matrix.mul_single_apply_of_ne (1 : A) j r w v hvr, mul_zero]

/-- Summing `X * E_{j, r} * E_{r, j}` over all columns `j` recovers `X`. -/
public theorem Matrix.sum_mul_single_one_mul_single_one {l m n A : Type*} [NonAssocSemiring A]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (X : Matrix l m A) (r : n) :
    ∑ j : m, X * Matrix.single j r (1 : A) * Matrix.single r j (1 : A) = X := by
  ext u v
  have hterm (j : m) :
      (X * Matrix.single j r (1 : A) * Matrix.single r j (1 : A)) u v =
        if v = j then X u j else 0 := by
    rcases eq_or_ne v j with rfl | hvj
    · simp only [↓reduceIte, Matrix.mul_single_apply_same, mul_one]
    · simp only [hvj, ↓reduceIte, Matrix.mul_single_apply_of_ne (1 : A) r j u v hvj]
  simp [Matrix.sum_apply, hterm]

/-- Summing `(X * E_{j₀, r}) * E_{r, s}(Y j₀ j₁)` over `j₀` gives `(X * Y) * E_{j₁, s}`. -/
public theorem Matrix.sum_mul_single_one_mul_single {l m n o p A : Type*} [NonAssocSemiring A]
    [Fintype m] [Fintype n] [Fintype o] [DecidableEq m] [DecidableEq n] [DecidableEq o]
    [DecidableEq p] (X : Matrix l m A) (Y : Matrix m n A) (j₁ : n) (r : o) (s : p) :
    ∑ j₀ : m, X * Matrix.single j₀ r (1 : A) * Matrix.single r s (Y j₀ j₁) =
      (X * Y) * Matrix.single j₁ s (1 : A) := by
  ext u v
  rcases eq_or_ne v s with rfl | hvs
  · rw [Matrix.sum_apply, Matrix.mul_single_apply_same, mul_one, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun j₀ _ ↦ by
      rw [Matrix.mul_single_apply_same, Matrix.mul_single_apply_same, mul_one]
  · rw [Matrix.sum_apply, Matrix.mul_single_apply_of_ne (1 : A) j₁ s u v hvs]
    exact Finset.sum_eq_zero fun j₀ _ ↦
      Matrix.mul_single_apply_of_ne (Y j₀ j₁) r s u v hvs _

/-- Summing `E_{r, s}(X j q) * E_{s, q}` over `q` places row `j` of `X` into row `r`, matching
`E_{r, j} * X`. -/
public theorem Matrix.sum_single_mul_single_one {l m n o A : Type*} [NonAssocSemiring A]
    [Fintype m] [Fintype n] [Fintype o] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    [DecidableEq o] (X : Matrix m n A) (j : m) (r : l) (s : o) :
    ∑ q : n, Matrix.single r s (X j q) * Matrix.single s q (1 : A) =
      Matrix.single r j (1 : A) * X := by
  ext u v
  rcases eq_or_ne u r with rfl | hur
  · rw [Matrix.sum_apply, Matrix.single_mul_apply_same, one_mul]
    have hterm (q : n) :
        (Matrix.single u s (X j q) * Matrix.single s q (1 : A)) u v =
          if v = q then X j q else 0 := by
      rw [Matrix.single_mul_single_same, mul_one]
      by_cases hvq : v = q <;> simp [Matrix.single, hvq, eq_comm]
    simp [hterm]
  · rw [Matrix.sum_apply, Matrix.single_mul_apply_of_ne (1 : A) r j u v hur]
    exact Finset.sum_eq_zero fun q _ ↦
      Matrix.single_mul_apply_of_ne (X j q) r s u v hur _

/-- Extracting entry `(j, p₀)` of `X` into position `(r, s)` by multiplying with unit matrix units
on both sides, valid without associativity of `A`. -/
public theorem Matrix.single_one_mul_mul_single_one {l m n o A : Type*} [NonAssocSemiring A]
    [Fintype m] [Fintype n] [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq o]
    (X : Matrix m n A) (j : m) (p₀ : n) (r : l) (s : o) :
    Matrix.single r j (1 : A) * (X * Matrix.single p₀ s (1 : A)) =
      Matrix.single r s (X j p₀) := by
  rw [Matrix.mul_mul_single_one, Matrix.single_mul_mul_single, one_mul, mul_one]

/-- Summing `E_{r, s}(X i u) * E_{s, t}(Y u j)` over `u` places `(X * Y) i j` in position
`(r, t)`. -/
public theorem Matrix.sum_single_mul_single {l m n o p q A : Type*} [NonUnitalNonAssocSemiring A]
    [Fintype m] [Fintype p] [DecidableEq o] [DecidableEq p] [DecidableEq q]
    (X : Matrix l m A) (Y : Matrix m n A) (i : l) (j : n) (r : o) (s : p) (t : q) :
    ∑ u : m, Matrix.single r s (X i u) * Matrix.single s t (Y u j) =
      Matrix.single r t ((X * Y) i j) := by
  simp_rw [Matrix.single_mul_single_same]
  ext u v
  simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.single]
