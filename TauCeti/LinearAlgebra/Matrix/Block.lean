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

An invertible block triangular matrix has invertible leading blocks over any commutative ring.
Consequently, multiplying on the left by an invertible block lower triangular matrix and on the
right by an invertible block upper triangular matrix preserves the condition that leading block
minors are units. This reduces the leading-minor test on a Bruhat expression `L * W * U` to the
test on its Weyl representative `W`. The middle matrix need not be invertible, the outer matrices
need not be unitriangular, and blocks may have arbitrary multiplicities. The result holds on any
down-closed set of block indices, including the empty set, before specializing to all initial
segments. In particular, it applies to weight-space blocks of arbitrary dimensions.

## Main results

* `Matrix.toBlocks₁₁_eq_submatrix`, `Matrix.toBlocks₁₂_eq_submatrix`,
  `Matrix.toBlocks₂₁_eq_submatrix`, and `Matrix.toBlocks₂₂_eq_submatrix`: block extraction
  as submatrix restriction.
* `Matrix.det_blockDiagonal'`: `(blockDiagonal' M).det = ∏ i, (M i).det`.
* `Matrix.BlockTriangular.toSquareBlockProp_mul_of_toDual` and
  `Matrix.BlockTriangular.toSquareBlockProp_mul`: square blocks of products on down-closed sets.
* `Matrix.isUnit_det_toSquareBlockProp_lt`: unit leading block minors give unit determinants of
  the leading blocks on the strict initial segments.
* `Matrix.BlockTriangular.isUnit_det_toSquareBlockProp`: leading blocks of an invertible
  block upper triangular matrix have unit determinants.
* `Matrix.BlockTriangular.isUnit_det_toSquareBlockProp_of_toDual`: the lower triangular version.
* `Matrix.isUnit_det_toSquareBlockProp_mul_mul_iff`: the unit-minor test on a down-closed set
  is unchanged by invertible triangular outer factors.
* `Matrix.forall_isUnit_det_toSquareBlockProp_le_mul_mul_iff`: preservation of the test on
  every leading block.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, second edition, AMS (2003),
  Part II, Chapter 1.
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

/-- Restricting to a square block commutes with any entrywise map. -/
@[simp]
public theorem map_toSquareBlockProp {m R S : Type*} (M : Matrix m m R) (p : m → Prop)
    (f : R → S) : (M.map f).toSquareBlockProp p = (M.toSquareBlockProp p).map f :=
  (rfl)

/-- A square block with unit determinant retains that property under a ring homomorphism. -/
public theorem _root_.IsUnit.det_map_toSquareBlockProp {m R S : Type*} [Fintype m]
    [DecidableEq m] [CommRing R] [CommRing S] {M : Matrix m m R} {p : m → Prop}
    [DecidablePred p] (h : IsUnit (M.toSquareBlockProp p).det) (f : R →+* S) :
    IsUnit ((M.map f).toSquareBlockProp p).det := by
  rw [map_toSquareBlockProp, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact h.map f

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
  rcases isEmpty_or_nonempty {j // b j < b i} with _ | _
  · simp
  obtain ⟨k, hk⟩ := Finite.exists_max fun j : {j // b j < b i} => b j
  rw [equiv_block_det M (q := fun j => b j ≤ b k) fun j =>
    ⟨fun hj => hj.trans_lt k.2, fun hj => hk ⟨j, hj⟩⟩]
  exact hM k

variable [DecidableEq m] [CommRing R] {A L M U : Matrix m m R} {p : m → Prop} [DecidablePred p]

/-- A leading block of a block upper triangular matrix with unit determinant also has unit
determinant. The set of indices may be any down-closed union of blocks. -/
public theorem BlockTriangular.isUnit_det_toSquareBlockProp (hA : A.BlockTriangular b)
    (hdet : IsUnit A.det) (hp : ∀ ⦃i j⦄, b j ≤ b i → p i → p j) :
    IsUnit (A.toSquareBlockProp p).det := by
  rw [twoBlockTriangular_det A p fun i hi j hj =>
    hA (lt_of_not_ge fun hij => hi (hp hij hj))] at hdet
  exact isUnit_of_mul_isUnit_left hdet

/-- A leading block of a block lower triangular matrix with unit determinant also has unit
determinant. The set of indices may be any down-closed union of blocks. -/
public theorem BlockTriangular.isUnit_det_toSquareBlockProp_of_toDual
    (hA : A.BlockTriangular (toDual ∘ b)) (hdet : IsUnit A.det)
    (hp : ∀ ⦃i j⦄, b j ≤ b i → p i → p j) :
    IsUnit (A.toSquareBlockProp p).det := by
  rw [twoBlockTriangular_det' A p fun i hi j hj =>
    hA (toDual_lt_toDual.mpr (lt_of_not_ge fun hij => hj (hp hij hi)))] at hdet
  exact isUnit_of_mul_isUnit_left hdet

/-- Invertible block lower triangular left factors and invertible block upper triangular right
factors preserve the unit-determinant test on every down-closed union of blocks. No hypothesis
on the middle matrix is required. -/
public theorem isUnit_det_toSquareBlockProp_mul_mul_iff
    (hL : L.BlockTriangular (toDual ∘ b)) (hU : U.BlockTriangular b)
    (hLdet : IsUnit L.det) (hUdet : IsUnit U.det)
    (hp : ∀ ⦃i j⦄, b j ≤ b i → p i → p j) :
    IsUnit ((L * M * U).toSquareBlockProp p).det ↔
      IsUnit (M.toSquareBlockProp p).det := by
  rw [hU.toSquareBlockProp_mul hp, hL.toSquareBlockProp_mul_of_toDual hp]
  simp only [det_mul, IsUnit.mul_iff,
    hL.isUnit_det_toSquareBlockProp_of_toDual hLdet hp,
    hU.isUnit_det_toSquareBlockProp hUdet hp, true_and, and_true]

/-- All leading block minors of `L * M * U` are units exactly when those of `M` are, if `L`
is invertible block lower triangular and `U` is invertible block upper triangular. This is the
leading-minor criterion for the block matrix big cell, invariant under its triangular factors. -/
public theorem forall_isUnit_det_toSquareBlockProp_le_mul_mul_iff
    (hL : L.BlockTriangular (toDual ∘ b)) (hU : U.BlockTriangular b)
    (hLdet : IsUnit L.det) (hUdet : IsUnit U.det) :
    (∀ i, IsUnit ((L * M * U).toSquareBlockProp fun j => b j ≤ b i).det) ↔
      ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det := by
  exact forall_congr' fun _ => isUnit_det_toSquareBlockProp_mul_mul_iff hL hU hLdet hUdet
    fun _ _ hji hi => hji.trans hi

end LeadingBlocks

end Matrix
