/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Products of matrix units

`Matrix.single_mul_single_eq_ite` combines the matching-index and unequal-index product
identities into one formula for rectangular matrix units with arbitrary coefficients.
Only the shared index type needs to be finite. `Matrix.smul_vecMulVec_single_single` writes a
scaled outer product of two coordinate vectors as a matrix unit, and
`Matrix.one_add_single_mul_one_add_single_of_ne` multiplies two elementary matrices `1 + c Eᵢⱼ`
and `1 + d Eₖₗ` with `j ≠ k`, whose cross term vanishes. `LinearMap.apply_eq_sum_sum_smul_single`
expands a linear map on matrices along the matrix units, and
`Matrix.submodule_eq_top_of_single_one_mem` shows that the matrix units span all matrices.

`Matrix.singleNonUnitalAlgHom` bundles the diagonal corner `x ↦ Matrix.single r r x` as a nonunital
algebra homomorphism, and `Matrix.singleNonUnitalStarRingHom` bundles the same corner as a
nonunital star ring homomorphism. They are accompanied by column, row, and entry matrix-unit
identities valid without associativity.

Two off-diagonal matrix units witness that transposition does not preserve all products.

`Matrix.single_eq_smul_single_one` writes a matrix with one nonzero entry `c` as `c` times the
corresponding matrix unit. For a homomorphism `f` out of `Mₙ(R)`,
`Matrix.map_single_mul_map_single` says that the images of the matrix units multiply like matrix
units, and `Matrix.star_map_single` that a `⋆`-homomorphism maps the adjoint `Eⱼᵢ` of `Eᵢⱼ` to the
adjoint of its image.
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

/-- A submodule of `Matrix m n R` that contains every matrix unit `single i j 1` is `⊤`. -/
public theorem Matrix.submodule_eq_top_of_single_one_mem {m n R : Type*} [Finite m] [Finite n]
    [DecidableEq m] [DecidableEq n] [Semiring R] {S : Submodule R (Matrix m n R)}
    (h : ∀ i j, Matrix.single i j (1 : R) ∈ S) : S = ⊤ := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  refine eq_top_iff.mpr fun A _ => ?_
  rw [Matrix.matrix_eq_sum_single A]
  refine S.sum_mem fun i _ => S.sum_mem fun j _ => ?_
  rw [← mul_one (A i j), ← smul_eq_mul, ← Matrix.smul_single]
  exact S.smul_mem _ (h i j)

/-- Transposition does not preserve all products of square matrices over a nontrivial semiring
when there are at least two indices. -/
public theorem Matrix.not_forall_transpose_mul (n R : Type*) [Fintype n] [Nontrivial n]
    [NonAssocSemiring R] [Nontrivial R] :
    ¬ ∀ x y : Matrix n n R, (x * y).transpose = x.transpose * y.transpose := by
  classical
  obtain ⟨i, j, hij⟩ := exists_pair_ne n
  intro h
  -- The matrix units at `(i, j)` and `(j, i)` multiply to the unit at `(i, i)` in one order and
  -- to the unit at `(j, j)` in the other, so the `(i, i)` entries differ.
  have hii := congrArg (fun m : Matrix n n R ↦ m i i)
    (h (Matrix.single i j 1) (Matrix.single j i 1))
  simp [Matrix.transpose_single, hij] at hii

public section
namespace Matrix

section SingleCorner
variable (R : Type*) {n A : Type*} [NonUnitalNonAssocSemiring A] [Fintype n] [DecidableEq n]

/-- The diagonal corner embedding `x ↦ Matrix.single r r x` as a nonunital algebra homomorphism. -/
def singleNonUnitalAlgHom [Monoid R] [DistribMulAction R A] (r : n) : A →ₙₐ[R] Matrix n n A where
  toFun := single r r; map_add' := single_add r r; map_zero' := single_zero r r
  map_smul' c x := (smul_single c r r x).symm
  map_mul' x y := (single_mul_single_same x r r r y).symm
/-- Evaluating `Matrix.singleNonUnitalAlgHom` places its input in the `(r, r)` entry. -/
@[simp] theorem singleNonUnitalAlgHom_apply [Monoid R] [DistribMulAction R A] (r : n) (x : A) :
    singleNonUnitalAlgHom R r x = single r r x := (rfl)
/-- The underlying `R`-linear map of `Matrix.singleNonUnitalAlgHom` is `Matrix.singleLinearMap`. -/
@[simp] theorem singleNonUnitalAlgHom_toLinearMap [Semiring R] [Module R A] (r : n) :
    (singleNonUnitalAlgHom R (A := A) r : A →ₗ[R] Matrix n n A) = singleLinearMap R r r := (rfl)
end SingleCorner

section SingleStarCorner
variable (A : Type*) {n : Type*} [NonUnitalNonAssocSemiring A] [StarRing A] [Fintype n]
  [DecidableEq n]

/-- The diagonal corner embedding `x ↦ Matrix.single r r x` as a nonunital star ring
homomorphism. -/
def singleNonUnitalStarRingHom (r : n) : A →⋆ₙ+* Matrix n n A where
  __ := (singleAddMonoidHom r r : A →+ Matrix n n A)
  map_mul' x y := (single_mul_single_same x r r r y).symm
  map_star' x := (conjTranspose_single r r x).symm
/-- Evaluating `Matrix.singleNonUnitalStarRingHom` places its input in the `(r, r)` entry. -/
@[simp] theorem singleNonUnitalStarRingHom_apply (r : n) (x : A) :
    singleNonUnitalStarRingHom A r x = single r r x := (rfl)
end SingleStarCorner

section NonAssoc
variable {l m n o p A : Type*} [NonAssocSemiring A]

/-- Placing column `j` of `X` into column `r` equals right multiplication by `E_{j, r}`. -/
theorem sum_single_eq_mul_single_one [Fintype l] [Fintype m] [DecidableEq l] [DecidableEq m]
    [DecidableEq n] (X : Matrix l m A) (j : m) (r : n) :
    ∑ u : l, single u r (X u j) = X * single j r (1 : A) := by
  ext u v; rcases eq_or_ne v r with rfl | hvr
  · rw [mul_single_apply_same, mul_one]; simp [single]
  · rw [mul_single_apply_of_ne (1 : A) j r u v hvr]; simp [single, hvr.symm]
/-- Right multiplication by `E_{j, r}` associates with matrix multiplication. -/
theorem mul_mul_single_one [Fintype m] [Fintype n] [DecidableEq n] [DecidableEq o]
    (X : Matrix l m A) (Y : Matrix m n A) (j : n) (r : o) :
    X * (Y * single j r (1 : A)) = (X * Y) * single j r (1 : A) := by
  ext u v; rcases eq_or_ne v r with rfl | hvr
  · rw [Matrix.mul_apply, mul_single_apply_same, mul_one, Matrix.mul_apply]
    simp [mul_single_apply_same]
  · simp [mul_single_apply_of_ne (1 : A) j r _ v hvr, Matrix.mul_apply]
/-- Summing `X * E_{j, r} * E_{r, j}` over all columns `j` recovers `X`. -/
theorem sum_mul_single_one_mul_single_one [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (X : Matrix l m A) (r : n) : ∑ j : m, X * single j r (1 : A) * single r j (1 : A) = X := by
  ext u v; rw [Matrix.sum_apply, Finset.sum_eq_single v]
  · simp [mul_single_apply_same]
  · exact fun j _ hne ↦ mul_single_apply_of_ne (1 : A) r j u v hne.symm _
  · exact fun hv ↦ absurd (Finset.mem_univ v) hv
/-- Summing `(X * E_{j₀, r}) * E_{r, s}(Y j₀ j₁)` over `j₀` gives `(X * Y) * E_{j₁, s}`. -/
theorem sum_mul_single_one_mul_single [Fintype m] [Fintype n] [Fintype o] [DecidableEq m]
    [DecidableEq n] [DecidableEq o] [DecidableEq p] (X : Matrix l m A) (Y : Matrix m n A)
    (j₁ : n) (r : o) (s : p) :
    ∑ j₀ : m, X * single j₀ r (1 : A) * single r s (Y j₀ j₁) = (X * Y) * single j₁ s (1 : A) := by
  ext u v; rcases eq_or_ne v s with rfl | hvs
  · rw [Matrix.sum_apply, mul_single_apply_same, mul_one, Matrix.mul_apply]
    simp [mul_single_apply_same]
  · simp [Matrix.sum_apply, mul_single_apply_of_ne _ _ s u v hvs]
/-- Summing `E_{r, s}(X j q) * E_{s, q}` over `q` places row `j` of `X` into row `r`. -/
theorem sum_single_mul_single_one [Fintype m] [Fintype n] [Fintype o] [DecidableEq l]
    [DecidableEq m] [DecidableEq n] [DecidableEq o] (X : Matrix m n A) (j : m) (r : l) (s : o) :
    ∑ q : n, single r s (X j q) * single s q (1 : A) = single r j (1 : A) * X := by
  ext u v; rcases eq_or_ne u r with rfl | hur
  · simp_rw [Matrix.sum_apply, single_mul_single_same, single_mul_apply_same, one_mul, mul_one]
    simp [single, eq_comm]
  · simp_rw [Matrix.sum_apply, single_mul_single_same, single_mul_apply_of_ne _ _ _ u v hur]
    simp [single, hur.symm]
/-- Extracting entry `(j, p₀)` of `X` into `(r, s)` via unit matrix units without associativity. -/
theorem single_one_mul_mul_single_one [Fintype m] [Fintype n] [DecidableEq l] [DecidableEq m]
    [DecidableEq n] [DecidableEq o] (X : Matrix m n A) (j : m) (p₀ : n) (r : l) (s : o) :
    single r j (1 : A) * (X * single p₀ s (1 : A)) = single r s (X j p₀) := by
  rw [mul_mul_single_one, single_mul_mul_single, one_mul, mul_one]
end NonAssoc

/-- Summing `E_{r, s}(X i u) * E_{s, t}(Y u j)` over `u` places `(X * Y) i j` in `(r, t)`. -/
theorem sum_single_mul_single {l m n o p q A : Type*} [NonUnitalNonAssocSemiring A] [Fintype m]
    [Fintype p] [DecidableEq o] [DecidableEq p] [DecidableEq q] (X : Matrix l m A)
    (Y : Matrix m n A) (i : l) (j : n) (r : o) (s : p) (t : q) :
    ∑ u : m, single r s (X i u) * single s t (Y u j) = single r t ((X * Y) i j) := by
  simp_rw [single_mul_single_same]; ext u v; simp [Matrix.sum_apply, Matrix.mul_apply, single]

/-- A matrix with one nonzero entry `c` is `c` times the corresponding matrix unit. -/
theorem single_eq_smul_single_one {m n R : Type*} [DecidableEq m] [DecidableEq n]
    [MulZeroOneClass R] (i : m) (j : n) (c : R) : single i j c = c • single i j (1 : R) := by
  rw [smul_single, smul_eq_mul, mul_one]

section MapSingle
variable {n R B F : Type*} [Fintype n] [DecidableEq n] [NonAssocSemiring R]
  [FunLike F (Matrix n n R) B]

/-- The images of the matrix units multiply like matrix units. -/
theorem map_single_mul_map_single [NonUnitalNonAssocSemiring B]
    [NonUnitalRingHomClass F (Matrix n n R) B] (f : F) (i j k l : n) :
    f (single i j 1) * f (single k l 1) = if j = k then f (single i l 1) else 0 := by
  rw [← map_mul]
  split_ifs with h
  · rw [h, single_mul_single_same, mul_one]
  · simp [h]

omit [Fintype n] in
/-- A `⋆`-homomorphism maps the adjoint `Eⱼᵢ` of a matrix unit `Eᵢⱼ` to the adjoint of its
image. -/
theorem star_map_single [StarRing R] [Star B] [StarHomClass F (Matrix n n R) B] (f : F)
    (i j : n) : star (f (single i j 1)) = f (single j i 1) := by
  rw [← map_star, star_eq_conjTranspose, conjTranspose_single, star_one]
end MapSingle
end Matrix
end
