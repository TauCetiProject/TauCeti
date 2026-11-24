/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Data.Matrix.Mul

/-!
# Matrix products: positivity of powers, nonvanishing of factors and opposite rings

Over a strictly ordered semiring, once some power `A ^ k` with `k > 0` of an entrywise nonnegative
square matrix `A` is strictly positive, every later power is strictly positive too: each row of `A`
has a positive entry, so multiplying a strictly positive matrix by `A` on the left keeps it
strictly positive. This is the form in which positivity propagates along the powers of a primitive
matrix.

If a product of matrices is nonzero, then the inner index type is nonempty and neither factor is
zero. A submatrix of a product can be computed through part of the inner index, provided the
relevant rows of the left factor vanish off that part. Products of matrices respect gradings of
their indices: the identity matrix and a product of degree-preserving matrices are
degree-preserving, and a product of matrices intertwining square matrices intertwines them.

Submatrices of an outer product `vecMulVec u v` are outer products of the reindexed vectors.

A scalar acting on the right factor of an outer product `vecMulVec (Pi.single i 1) v` may be pulled
out to the left without any commutativity, since the left factor has entries `0` and `1` only.

Transposing a product of rectangular matrices and passing to the opposite ring reverses the
factors; transposition with `MulOpposite.op` and with `MulOpposite.unop` are mutually inverse.

Sandwiching a matrix over an `R`-algebra between two matrices with entries in `R` gives entries that
are `R`-linear combinations of the entries of the middle factor.

## Main results

* `Matrix.pow_apply_pos_of_le`: if `A` is entrywise nonnegative and `A ^ k` is strictly positive
  for some `k > 0`, then so is `A ^ m` for every `m ≥ k`.
* `Matrix.nonempty_of_mul_ne_zero`, `Matrix.left_ne_zero_of_mul_ne_zero`,
  `Matrix.right_ne_zero_of_mul_ne_zero`: if a matrix product is nonzero, then the inner index type
  is nonempty and neither factor is zero.
* `Matrix.submatrix_mul_of_injective`: a submatrix of a product is the product of submatrices
  through an injective inner reindexing whose range carries the relevant rows of the left factor.
* `Matrix.eq_of_mul_apply_ne_zero`: a product of degree-preserving matrices is degree-preserving.
* `Matrix.eq_of_one_apply_ne_zero`: the identity matrix is degree-preserving.
* `Matrix.mul_mul_eq_mul_mul_of_mul_eq_mul`: if `D₁ * X = X * D₂` and `D₂ * Y = Y * D₃`, then
  `D₁ * (X * Y) = X * Y * D₃`.
* `Matrix.vecMulVec_single_one_smul`: `vecMulVec (Pi.single i 1) (r • v) = r • vecMulVec
  (Pi.single i 1) v`, for any scalar action, unlike `Matrix.vecMulVec_smul`.
* `Matrix.submatrix_vecMulVec`: a submatrix of an outer product is the outer product of the
  reindexed vectors.
* `Matrix.transpose_mul_map_op`: transposing a product and passing to the opposite ring reverses
  the factors, `(M * N)ᵀ.map op = Nᵀ.map op * Mᵀ.map op`, for rectangular `M` and `N`.
* `Matrix.map_algebraMap_mul_mul_map_algebraMap_apply`: the entries of `F * u * G`, for `F` and
  `G` with entries in `R` and `u` over an `R`-algebra, are `∑ q, ∑ p, (F i p * G q j) • u p q`.
-/

public section

open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section StrictOrderedSemiring

variable {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {A : Matrix n n R}

/-- If `A` is entrywise nonnegative and its power `A ^ k`, for some `k > 0`, is strictly positive,
then every power `A ^ m` with `m ≥ k` is strictly positive. -/
theorem pow_apply_pos_of_le (hA : ∀ i j, 0 ≤ A i j) {k : ℕ} (hk : 0 < k)
    (hAk : ∀ i j, 0 < (A ^ k) i j) {m : ℕ} (hkm : k ≤ m) : ∀ i j, 0 < (A ^ m) i j := by
  -- Every row of `A` has a positive entry, since `A ^ k = A * A ^ (k - 1)` does.
  have hrow : ∀ i, ∃ l, 0 < A i l := fun i => by
    have h := hAk i i
    rw [← Nat.sub_add_cancel hk, pow_succ', Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
    exact ⟨l, (hA i l).lt_of_ne' (left_ne_zero_of_mul hl)⟩
  induction m, hkm using Nat.le_induction with
  | base => exact hAk
  | succ m _ ih =>
    intro i j
    obtain ⟨l, hl⟩ := hrow i
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_pos' (fun l _ => mul_nonneg (hA i l) (ih l j).le)
      ⟨l, Finset.mem_univ l, mul_pos hl (ih l j)⟩

end StrictOrderedSemiring

section NonUnitalNonAssocSemiring

variable {K : Type*} [NonUnitalNonAssocSemiring K] {m n p : Type*} [Fintype n]

/-- If a matrix product is nonzero, then the inner index type is nonempty. -/
theorem nonempty_of_mul_ne_zero {A : Matrix m n K} {B : Matrix n p K} (h : A * B ≠ 0) :
    Nonempty n := by
  by_contra hn
  have := not_nonempty_iff.mp hn
  exact h (Matrix.ext fun i j ↦ by simp [Matrix.mul_apply])

/-- If a matrix product is nonzero, then its left factor is nonzero. -/
theorem left_ne_zero_of_mul_ne_zero {A : Matrix m n K} {B : Matrix n p K} (h : A * B ≠ 0) :
    A ≠ 0 := fun hA ↦ h (by simp [hA])

/-- If a matrix product is nonzero, then its right factor is nonzero. -/
theorem right_ne_zero_of_mul_ne_zero {A : Matrix m n K} {B : Matrix n p K} (h : A * B ≠ 0) :
    B ≠ 0 := fun hB ↦ h (by simp [hB])

/-- The rows `e₁` and columns `e₃` of a matrix product can be computed through the inner indices
`e₂` alone, when `e₂` is injective and the rows `e₁` of the left factor vanish outside its range.
For a bijective `e₂` this is `Matrix.submatrix_mul`. -/
theorem submatrix_mul_of_injective {l o q : Type*} [Fintype o] (A : Matrix m n K)
    (B : Matrix n p K) (e₁ : l → m) (e₂ : o → n) (e₃ : q → p) (he₂ : Function.Injective e₂)
    (hA : ∀ i j, A (e₁ i) j ≠ 0 → j ∈ Set.range e₂) :
    (A * B).submatrix e₁ e₃ = A.submatrix e₁ e₂ * B.submatrix e₂ e₃ :=
  ext fun i k ↦ (Fintype.sum_of_injective e₂ he₂ _ _
    (fun j hj ↦ by simp [not_ne_iff.mp (mt (hA i j) hj)]) fun _ ↦ rfl).symm

/-- **Products preserve degrees.** If the nonzero entries `A i j` and `B j k` of two matrices
only join indices of the same degree, so do the nonzero entries of `A * B`. -/
theorem eq_of_mul_apply_ne_zero {G : Type*} {g₁ : m → G} {g₂ : n → G} {g₃ : p → G}
    {A : Matrix m n K} {B : Matrix n p K} (hA : ∀ i j, A i j ≠ 0 → g₂ j = g₁ i)
    (hB : ∀ j k, B j k ≠ 0 → g₃ k = g₂ j) (i : m) (k : p) (h : (A * B) i k ≠ 0) :
    g₃ k = g₁ i := by
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [hB j k (right_ne_zero_of_mul hj), hA i j (left_ne_zero_of_mul hj)]

end NonUnitalNonAssocSemiring

section ZeroOne

variable {R m : Type*} [Zero R] [One R] [DecidableEq m]

/-- **The identity matrix preserves degrees.** The nonzero entries of `1` only join indices of the
same degree. -/
theorem eq_of_one_apply_ne_zero {G : Type*} {g : m → G} (i k : m)
    (h : (1 : Matrix m m R) i k ≠ 0) : g k = g i := by
  obtain rfl : i = k := by_contra fun hik ↦ h (one_apply_ne hik)
  rfl

end ZeroOne

section NonUnitalSemiring

variable {R ν₁ ν₂ ν₃ : Type*} [NonUnitalSemiring R]

/-- A product of matrices intertwining square matrices intertwines them: if `D₁ * X = X * D₂` and
`D₂ * Y = Y * D₃`, then `D₁ * (X * Y) = X * Y * D₃`. This is the analogue of `SemiconjBy.mul_left`
for rectangular matrices. -/
theorem mul_mul_eq_mul_mul_of_mul_eq_mul [Fintype ν₁] [Fintype ν₂] [Fintype ν₃]
    {D₁ : Matrix ν₁ ν₁ R} {D₂ : Matrix ν₂ ν₂ R} {D₃ : Matrix ν₃ ν₃ R} {X : Matrix ν₁ ν₂ R}
    {Y : Matrix ν₂ ν₃ R} (hX : D₁ * X = X * D₂) (hY : D₂ * Y = Y * D₃) :
    D₁ * (X * Y) = X * Y * D₃ := by
  rw [← Matrix.mul_assoc, hX, Matrix.mul_assoc, hY, Matrix.mul_assoc]

end NonUnitalSemiring

section MulZeroOneClass

variable {α R m p : Type*} [MulZeroOneClass α] [SMulZeroClass R α] [DecidableEq m]

/-- A scalar on the right factor of an outer product with `Pi.single i 1` may be pulled out to the
left. Unlike `Matrix.vecMulVec_smul`, this needs no `SMulCommClass R α α`, because the entries of
`Pi.single i 1` are `0` and `1`; so it applies, for instance, to left multiplication in a
noncommutative ring. -/
@[simp]
theorem vecMulVec_single_one_smul (r : R) (i : m) (v : p → α) :
    vecMulVec (Pi.single i (1 : α)) (r • v) = r • vecMulVec (Pi.single i (1 : α)) v := by
  ext a b
  rcases eq_or_ne a i with rfl | h
  · simp [vecMulVec_apply]
  · simp [vecMulVec_apply, h]

end MulZeroOneClass

/-- A submatrix of an outer product is the outer product of the reindexed vectors. -/
@[simp]
theorem submatrix_vecMulVec {α l m n o : Type*} [Mul α] (u : m → α) (v : n → α) (f : l → m)
    (g : o → n) : (vecMulVec u v).submatrix f g = vecMulVec (u ∘ f) (v ∘ g) := by
  ext
  simp [vecMulVec_apply]

section MulOpposite

variable {α m n p : Type*}

/-- Transposing a matrix and passing to the opposite ring, then transposing back and returning to
the ring, gives the original matrix. -/
@[simp]
theorem transpose_map_op_transpose_map_unop (M : Matrix m n α) :
    (Mᵀ.map MulOpposite.op)ᵀ.map MulOpposite.unop = M :=
  rfl

/-- Transposing a matrix over the opposite ring and returning to the ring, then transposing back
and passing to the opposite ring, gives the original matrix. -/
@[simp]
theorem transpose_map_unop_transpose_map_op (M : Matrix m n αᵐᵒᵖ) :
    (Mᵀ.map MulOpposite.unop)ᵀ.map MulOpposite.op = M :=
  rfl

/-- Transposing a product of matrices and passing to the opposite ring reverses the factors. -/
theorem transpose_mul_map_op [Mul α] [AddCommMonoid α] [Fintype n] (M : Matrix m n α)
    (N : Matrix n p α) :
    (M * N)ᵀ.map MulOpposite.op = Nᵀ.map MulOpposite.op * Mᵀ.map MulOpposite.op := by
  ext i j
  simp [Matrix.mul_apply]

end MulOpposite

/-- The entries of a matrix over an `R`-algebra `A` sandwiched between two matrices over `R` are
`R`-linear combinations of its entries. -/
theorem map_algebraMap_mul_mul_map_algebraMap_apply {R A l m n o : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [Fintype m] [Fintype n] (F : Matrix l m R) (u : Matrix m n A)
    (G : Matrix n o R) (i : l) (j : o) :
    (F.map (algebraMap R A) * u * G.map (algebraMap R A)) i j =
      ∑ q, ∑ p, (F i p * G q j) • u p q := by
  simp only [Matrix.mul_apply, map_apply, Finset.sum_mul, Algebra.smul_def, map_mul]
  refine Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun p _ ↦ ?_
  rw [mul_assoc, ← Algebra.commutes (G q j), ← mul_assoc]

end Matrix
