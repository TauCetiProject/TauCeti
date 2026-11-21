/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul

/-!
# Matrix products: powers, nonvanishing, outer products, and opposite transposes

Over a strictly ordered semiring, once some power `A ^ k` with `k > 0` of an entrywise nonnegative
square matrix `A` is strictly positive, every later power is strictly positive too: each row of `A`
has a positive entry, so multiplying a strictly positive matrix by `A` on the left keeps it
strictly positive. This is the form in which positivity propagates along the powers of a primitive
matrix.

If a product of matrices is nonzero, then the inner index type is nonempty and neither factor is
zero.

Submatrices of an outer product `vecMulVec u v` are outer products of the reindexed vectors.

A scalar acting on the right factor of an outer product `vecMulVec (Pi.single i 1) v` may be pulled
out to the left without any commutativity, since the left factor has entries `0` and `1` only.

Over noncommutative rings, transpose followed by entrywise `MulOpposite.op` or `MulOpposite.unop`
reverses matrix multiplication and intertwines column-vector multiplication with row-vector
multiplication.

## Main results

* `Matrix.pow_apply_pos_of_le`: if `A` is entrywise nonnegative and `A ^ k` is strictly positive
  for some `k > 0`, then so is `A ^ m` for every `m ≥ k`.
* `Matrix.nonempty_of_mul_ne_zero`, `Matrix.left_ne_zero_of_mul_ne_zero`,
  `Matrix.right_ne_zero_of_mul_ne_zero`: if a matrix product is nonzero, then the inner index type
  is nonempty and neither factor is zero.
* `Matrix.vecMulVec_single_one_smul`: `vecMulVec (Pi.single i 1) (r • v) = r • vecMulVec
  (Pi.single i 1) v`, for any scalar action, unlike `Matrix.vecMulVec_smul`.
* `Matrix.submatrix_vecMulVec`: a submatrix of an outer product is the outer product of the
  reindexed vectors.
* `Matrix.transpose_map_op_mul`, `Matrix.transpose_map_unop_mul`, `Matrix.op_comp_mulVec`,
  `Matrix.transpose_map_op_map_ringHom_op`: opposite-entry transpose reverses matrix
  multiplication, intertwines `mulVec` with `vecMul`, and commutes with entrywise ring
  homomorphisms.
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

end NonUnitalNonAssocSemiring

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

end Matrix

section MulOpposite

open MulOpposite

namespace Matrix

variable {l m n R : Type*}

/-- Over any type with multiplication and commutative addition, transpose followed by entrywise
`MulOpposite.op` reverses matrix multiplication. -/
theorem transpose_map_op_mul [Fintype n] [Mul R] [AddCommMonoid R]
    (x : Matrix m n R) (y : Matrix n l R) :
    y.transpose.map op * x.transpose.map op = (x * y).transpose.map op := by
  ext i j
  simp [Matrix.mul_apply]

/-- Over any type with multiplication and commutative addition, transpose followed by entrywise
`MulOpposite.unop` reverses matrix multiplication. -/
theorem transpose_map_unop_mul [Fintype n] [Mul R] [AddCommMonoid R]
    (x : Matrix m n Rᵐᵒᵖ) (y : Matrix n l Rᵐᵒᵖ) :
    y.transpose.map unop * x.transpose.map unop = (x * y).transpose.map unop := by
  ext i j
  simp [Matrix.mul_apply]

/-- Applying `MulOpposite.op` to each coordinate intertwines matrix-vector multiplication by `M`
with vector-matrix multiplication by `Mᵀ.map op`. -/
theorem op_comp_mulVec [NonUnitalNonAssocSemiring R] [Fintype n]
    (M : Matrix m n R) (v : n → R) :
    op ∘ (M *ᵥ v) = (op ∘ v) ᵥ* M.transpose.map op := by
  ext i
  simp [mulVec, vecMul, dotProduct]

/-- Applying `RingHom.op f` entrywise to `Mᵀ.map op` commutes with `(·)ᵀ.map op`. -/
theorem transpose_map_op_map_ringHom_op {S : Type*} [NonAssocSemiring R] [NonAssocSemiring S]
    (M : Matrix m n R) (f : R →+* S) :
    (M.transpose.map op).map (RingHom.op f) = (M.map f).transpose.map op :=
  rfl

end Matrix

end MulOpposite
