/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Block matrix identities

The four blocks extracted from a matrix on sum index types are its submatrices along the
corresponding sum injections. These identities connect the block and submatrix APIs.

The determinant of a block-diagonal matrix `Matrix.blockDiagonal' M` whose blocks may have
different index types is the product of the determinants of its blocks. This is the dependent
version of Mathlib's `Matrix.det_blockDiagonal`, and computes the determinant of a coordinatewise
endomorphism of a finite dependent product.

On a set of indices that is down-closed for a ranking `b`, the square block of a product with a
block lower triangular left factor, or a block upper triangular right factor, is the product of
the square blocks. If the leading blocks on the initial segments `{j | b j ≤ b i}` have unit
determinants, so do the leading blocks on the strict initial segments `{j | b j < b i}`.

## Main results

* `Matrix.toBlocks₁₁_eq_submatrix`, `Matrix.toBlocks₁₂_eq_submatrix`,
  `Matrix.toBlocks₂₁_eq_submatrix`, and `Matrix.toBlocks₂₂_eq_submatrix`: block extraction
  as submatrix restriction.
* `Matrix.det_blockDiagonal'`: `(blockDiagonal' M).det = ∏ i, (M i).det`.
* `Matrix.BlockTriangular.toSquareBlockProp_mul_of_toDual` and
  `Matrix.BlockTriangular.toSquareBlockProp_mul`: square blocks of products on down-closed sets.
* `Matrix.isUnit_det_toSquareBlockProp_lt`: unit leading block minors give unit determinants of
  the leading blocks on the strict initial segments.
-/

open OrderDual

namespace Matrix

-- Keep these bridges as explicit rewrite rules so block expressions retain their simp normal form.
/-- The upper-left block is the submatrix along the left sum injections. -/
public theorem toBlocks₁₁_eq_submatrix {m n p q α : Type*} (M : Matrix (m ⊕ n) (p ⊕ q) α) :
    M.toBlocks₁₁ = M.submatrix Sum.inl Sum.inl :=
  (rfl)

/-- The upper-right block restricts rows along the left injection and columns along the right. -/
public theorem toBlocks₁₂_eq_submatrix {m n p q α : Type*} (M : Matrix (m ⊕ n) (p ⊕ q) α) :
    M.toBlocks₁₂ = M.submatrix Sum.inl Sum.inr :=
  (rfl)

/-- The lower-left block restricts rows along the right injection and columns along the left. -/
public theorem toBlocks₂₁_eq_submatrix {m n p q α : Type*} (M : Matrix (m ⊕ n) (p ⊕ q) α) :
    M.toBlocks₂₁ = M.submatrix Sum.inr Sum.inl :=
  (rfl)

/-- The lower-right block is the submatrix along the right sum injections. -/
public theorem toBlocks₂₂_eq_submatrix {m n p q α : Type*} (M : Matrix (m ⊕ n) (p ⊕ q) α) :
    M.toBlocks₂₂ = M.submatrix Sum.inr Sum.inr :=
  (rfl)

/-- The determinant of a block-diagonal matrix with blocks of possibly different sizes is the
product of the determinants of the blocks. This is the dependent version of
`Matrix.det_blockDiagonal`. -/
@[simp]
public theorem det_blockDiagonal' {o R : Type*} {m : o → Type*} [Fintype o] [DecidableEq o]
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] [CommRing R] (M : ∀ i, Matrix (m i) (m i) R) :
    (blockDiagonal' M).det = ∏ i, (M i).det := by
  -- `BlockTriangular.det_fintype` needs a linear order on the block indices; any one will do.
  let _ : LinearOrder o := Equiv.linearOrder (Fintype.equivFin o)
  rw [(blockTriangular_blockDiagonal' M).det_fintype]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← det_reindex_self (Equiv.sigmaSubtype i)]
  congr 1
  ext j k
  -- The `@[simps]` lemmas of `Equiv.sigmaSubtype` only give the first component of
  -- `(Equiv.sigmaSubtype i).symm j`, so the definition is unfolded to see that it is `⟨i, j⟩`.
  simp [toSquareBlock_def, Equiv.sigmaSubtype]

/-! ### Leading blocks -/

section LeadingBlocks

variable {m R α : Type*} [Fintype m] [LinearOrder α] {b : m → α}

/-- **Leading blocks of a product with a block lower triangular left factor.** If `A` is block
lower triangular for `b` and `p` picks out a set of indices that is down-closed for `b`, then the
square block of `A * B` on `p` is the product of the square blocks of `A` and `B` on `p`. -/
public theorem BlockTriangular.toSquareBlockProp_mul_of_toDual [NonUnitalNonAssocSemiring R]
    {A : Matrix m m R} (hA : A.BlockTriangular (toDual ∘ b)) {p : m → Prop} [DecidablePred p]
    (hp : ∀ ⦃i j⦄, b j ≤ b i → p i → p j) (B : Matrix m m R) :
    (A * B).toSquareBlockProp p = A.toSquareBlockProp p * B.toSquareBlockProp p := by
  ext i j
  simp only [toSquareBlockProp_def, of_apply, Matrix.mul_apply]
  refine (Fintype.sum_subtype_add_sum_subtype p fun k => A i k * B k j).symm.trans ?_
  rw [Fintype.sum_eq_zero (fun k : {k // ¬p k} => A i k * B k j) fun k => ?_, add_zero]
  have hik : b i < b k := lt_of_not_ge fun h => k.2 (hp h i.2)
  rw [hA (toDual_lt_toDual.mpr hik), zero_mul]

/-- **Leading blocks of a product with a block upper triangular right factor.** If `A` is block
upper triangular for `b` and `p` picks out a set of indices that is down-closed for `b`, then the
square block of `B * A` on `p` is the product of the square blocks of `B` and `A` on `p`. -/
public theorem BlockTriangular.toSquareBlockProp_mul [NonUnitalNonAssocSemiring R]
    {A : Matrix m m R} (hA : A.BlockTriangular b) {p : m → Prop} [DecidablePred p]
    (hp : ∀ ⦃i j⦄, b j ≤ b i → p i → p j) (B : Matrix m m R) :
    (B * A).toSquareBlockProp p = B.toSquareBlockProp p * A.toSquareBlockProp p := by
  ext i j
  simp only [toSquareBlockProp_def, of_apply, Matrix.mul_apply]
  refine (Fintype.sum_subtype_add_sum_subtype p fun k => B i k * A k j).symm.trans ?_
  rw [Fintype.sum_eq_zero (fun k : {k // ¬p k} => B i k * A k j) fun k => ?_, add_zero]
  rw [hA (lt_of_not_ge fun h => k.2 (hp h j.2)), mul_zero]

/-- If every leading block of `M` has a unit determinant, so does every leading block on a strict
initial segment `{j | b j < b i}`: that segment is either empty or a leading segment itself. -/
public theorem isUnit_det_toSquareBlockProp_lt [DecidableEq m] [CommRing R] (M : Matrix m m R)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det) (i : m) :
    IsUnit (M.toSquareBlockProp fun j => b j < b i).det := by
  by_cases hne : (Finset.univ.filter fun j => b j < b i).Nonempty
  · obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image _ b hne
    rw [Finset.mem_filter] at hk
    rw [equiv_block_det M fun j => ⟨fun hj => lt_of_le_of_lt hj hk.2,
      fun hj => hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)⟩]
    exact hM k
  · have : IsEmpty {j // b j < b i} :=
      ⟨fun j => hne ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.2⟩⟩⟩
    rw [det_isEmpty]
    exact isUnit_one

end LeadingBlocks

end Matrix
