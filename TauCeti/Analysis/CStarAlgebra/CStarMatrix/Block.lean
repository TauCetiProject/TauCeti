/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Block
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Rectangular
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.LinearAlgebra.Matrix.Hermitian
import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block

/-!
# Block matrices, corner embeddings, and block operator norms on `CStarMatrix`

Building on the rectangular `CStarMatrix` calculus, this file develops `2 × 2` block matrices and
standard corner/diagonal `⋆`-algebra embeddings for `CStarMatrix`:

* Block matrices `CStarMatrix.fromBlocks`, their algebraic and star operations, block-diagonal
  characterizations of self-adjointness and unitarity, and reindexing under
  `Equiv.sumCongr`, `Equiv.sumComm`, and `Equiv.sumAssoc`.
* Block-diagonal `⋆`-algebra embedding `CStarMatrix.blockDiagStarAlgHom`, corner embeddings
  `CStarMatrix.inl` and `CStarMatrix.inr`, matrix units `CStarMatrix.single` and
  `CStarMatrix.singleStarAlgHom`, and diagonal matrices `CStarMatrix.diagonal` and
  `CStarMatrix.diagonalStarAlgHom`.
* Exact operator-norm formulas `‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖` and
  `‖fromBlocks 0 M N 0‖ = max ‖M‖ ‖N‖` for arbitrary rectangular blocks `M` and `N`, together with
  isometry lemmas for `inl`, `inr`, `singleStarAlgHom`, `single`, and `diagonal`.

## Main declarations

* `CStarMatrix.fromBlocks`: `2 × 2` block matrices in `CStarMatrix (n ⊕ o) (l ⊕ m) A`.
* `CStarMatrix.blockDiagStarAlgHom`: `⋆`-algebra embedding `(M, N) ↦ fromBlocks M 0 0 N`.
* `CStarMatrix.inl`, `CStarMatrix.inr`, `CStarMatrix.singleStarAlgHom`,
  `CStarMatrix.diagonalStarAlgHom`: isometric `⋆`-algebra corner and diagonal embeddings.
* `CStarMatrix.norm_fromBlocks_zero₁₂_zero₂₁`, `CStarMatrix.norm_fromBlocks_zero₁₁_zero₂₂`: exact
  operator-norm formulas `max ‖M‖ ‖N‖` for diagonal and anti-diagonal `2 × 2` block matrices.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §3.1 and §4.1.
* M. Rørdam, F. Larsen, and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, Chapter 2.
-/

public section

open scoped Matrix

namespace CStarMatrix

section FromBlocks

variable {k l m n o p q r R A B : Type*}

/-- Assemble four `CStarMatrix` blocks into a `(n ⊕ o) × (l ⊕ m)` matrix. -/
def fromBlocks (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A) : CStarMatrix (n ⊕ o) (l ⊕ m) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
    (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂))

/-- Reading `fromBlocks` as an ordinary `Matrix` yields `Matrix.fromBlocks`. -/
@[simp] theorem ofMatrix_symm_fromBlocks (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A) :
    ofMatrix.symm (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
        (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂) := (rfl)

/-- `ofMatrix` transports `Matrix.fromBlocks` to `CStarMatrix.fromBlocks`. -/
@[simp] theorem of_fromBlocks (M₁₁ : Matrix n l A) (M₁₂ : Matrix n m A)
    (M₂₁ : Matrix o l A) (M₂₂ : Matrix o m A) :
    ofMatrix (Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (ofMatrix M₁₁) (ofMatrix M₁₂) (ofMatrix M₂₁) (ofMatrix M₂₂) := (rfl)

@[simp] theorem fromBlocks_apply₁₁ (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A) (i : n) (j : l) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inl j) = M₁₁ i j := (rfl)

@[simp] theorem fromBlocks_apply₁₂ (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A) (i : n) (j : m) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inr j) = M₁₂ i j := (rfl)

@[simp] theorem fromBlocks_apply₂₁ (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A) (i : o) (j : l) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inl j) = M₂₁ i j := (rfl)

@[simp] theorem fromBlocks_apply₂₂ (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A) (i : o) (j : m) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inr j) = M₂₂ i j := (rfl)

@[simp] theorem fromBlocks_inj {M₁₁ N₁₁ : CStarMatrix n l A} {M₁₂ N₁₂ : CStarMatrix n m A}
    {M₂₁ N₂₁ : CStarMatrix o l A} {M₂₂ N₂₂ : CStarMatrix o m A} :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ ↔
      M₁₁ = N₁₁ ∧ M₁₂ = N₁₂ ∧ M₂₁ = N₂₁ ∧ M₂₂ = N₂₂ := Matrix.fromBlocks_inj

@[simp] theorem fromBlocks_zero [Zero A] :
    fromBlocks (0 : CStarMatrix n l A) (0 : CStarMatrix n m A)
      (0 : CStarMatrix o l A) (0 : CStarMatrix o m A) = 0 := Matrix.fromBlocks_zero

@[simp] theorem fromBlocks_one [DecidableEq l] [DecidableEq m] [Zero A] [One A] :
    fromBlocks (1 : CStarMatrix l l A) 0 0 (1 : CStarMatrix m m A) = 1 := Matrix.fromBlocks_one

theorem fromBlocks_add [Add A] (M₁₁ N₁₁ : CStarMatrix n l A) (M₁₂ N₁₂ : CStarMatrix n m A)
    (M₂₁ N₂₁ : CStarMatrix o l A) (M₂₂ N₂₂ : CStarMatrix o m A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ + fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ + N₁₁) (M₁₂ + N₁₂) (M₂₁ + N₂₁) (M₂₂ + N₂₂) :=
  Matrix.fromBlocks_add M₁₁ M₁₂ M₂₁ M₂₂ N₁₁ N₁₂ N₂₁ N₂₂

theorem fromBlocks_neg [Neg A] (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A) :
    -fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks (-M₁₁) (-M₁₂) (-M₂₁) (-M₂₂) :=
  Matrix.fromBlocks_neg M₁₁ M₁₂ M₂₁ M₂₂

theorem fromBlocks_sub [Sub A] (M₁₁ N₁₁ : CStarMatrix n l A) (M₁₂ N₁₂ : CStarMatrix n m A)
    (M₂₁ N₂₁ : CStarMatrix o l A) (M₂₂ N₂₂ : CStarMatrix o m A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ - fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ - N₁₁) (M₁₂ - N₁₂) (M₂₁ - N₂₁) (M₂₂ - N₂₂) := by
  ext (_ | _) (_ | _) <;> rfl

theorem fromBlocks_smul [SMul R A] (c : R) (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A) :
    c • fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks (c • M₁₁) (c • M₁₂) (c • M₂₁) (c • M₂₂) :=
  Matrix.fromBlocks_smul c M₁₁ M₁₂ M₂₁ M₂₂

theorem fromBlocks_multiply [Fintype l] [Fintype m] [NonUnitalNonAssocSemiring A]
    (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A)
    (N₁₁ : CStarMatrix l p A) (N₁₂ : CStarMatrix l q A)
    (N₂₁ : CStarMatrix m p A) (N₂₂ : CStarMatrix m q A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ * N₁₁ + M₁₂ * N₂₁) (M₁₁ * N₁₂ + M₁₂ * N₂₂)
        (M₂₁ * N₁₁ + M₂₂ * N₂₁) (M₂₁ * N₁₂ + M₂₂ * N₂₂) :=
  Matrix.fromBlocks_multiply M₁₁ M₁₂ M₂₁ M₂₂ N₁₁ N₁₂ N₂₁ N₂₂

theorem fromBlocks_map (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A) (f : A → B) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).map f =
      fromBlocks (M₁₁.map f) (M₁₂.map f) (M₂₁.map f) (M₂₂.map f) :=
  Matrix.fromBlocks_map M₁₁ M₁₂ M₂₁ M₂₂ f

theorem fromBlocks_transpose (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).transpose =
      fromBlocks M₁₁.transpose M₂₁.transpose M₁₂.transpose M₂₂.transpose :=
  Matrix.fromBlocks_transpose M₁₁ M₁₂ M₂₁ M₂₂

theorem fromBlocks_conjTranspose [Star A] (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).conjTranspose =
      fromBlocks M₁₁.conjTranspose M₂₁.conjTranspose M₁₂.conjTranspose M₂₂.conjTranspose :=
  Matrix.fromBlocks_conjTranspose M₁₁ M₁₂ M₂₁ M₂₂

/-- `star` of a square `2 × 2` block `CStarMatrix` transposes the off-diagonal blocks and applies
`star` to the diagonal blocks. -/
theorem star_fromBlocks [Star A] (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix n m A) (M₂₂ : CStarMatrix n n A) :
    star (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (star M₁₁) M₂₁.conjTranspose M₁₂.conjTranspose (star M₂₂) :=
  fromBlocks_conjTranspose M₁₁ M₁₂ M₂₁ M₂₂

/-- Entrywise `mapₙₐ` distributes across `fromBlocks`. -/
theorem mapₙₐ_fromBlocks [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (f : A →⋆ₙₐ[R] B)
    (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix n m A) (M₂₂ : CStarMatrix n n A) :
    mapₙₐ f (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (mapₙₐ f M₁₁) (M₁₂.map f) (M₂₁.map f) (mapₙₐ f M₂₂) :=
  fromBlocks_map M₁₁ M₁₂ M₂₁ M₂₂ f

/-- Entrywise `mapₙₐ` commutes with block-diagonal direct sums. -/
theorem mapₙₐ_fromBlocks_zero₁₂_zero₂₁ [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (f : A →⋆ₙₐ[R] B)
    (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    mapₙₐ f (fromBlocks M 0 0 N) = fromBlocks (mapₙₐ f M) 0 0 (mapₙₐ f N) := by
  rw [mapₙₐ_fromBlocks]; congr 1 <;> ext <;> simp

private theorem isSelfAdjoint_iff_isHermitian_ofMatrix_symm {k A : Type*} [InvolutiveStar A]
    (X : CStarMatrix k k A) : IsSelfAdjoint X ↔ (ofMatrix.symm X).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSelfAdjoint]
  exact ofMatrix.symm.injective.eq_iff.symm

/-- A square `2 × 2` block `CStarMatrix` is self-adjoint iff its diagonal blocks are self-adjoint
and its off-diagonal blocks are conjugate transposes of each other. -/
theorem isSelfAdjoint_fromBlocks_iff [InvolutiveStar A]
    {M₁₁ : CStarMatrix m m A} {M₁₂ : CStarMatrix m n A}
    {M₂₁ : CStarMatrix n m A} {M₂₂ : CStarMatrix n n A} :
    IsSelfAdjoint (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) ↔
      IsSelfAdjoint M₁₁ ∧ M₁₂.conjTranspose = M₂₁ ∧ IsSelfAdjoint M₂₂ := by
  rw [isSelfAdjoint_iff_isHermitian_ofMatrix_symm, ofMatrix_symm_fromBlocks,
    Matrix.isHermitian_fromBlocks_iff, ← isSelfAdjoint_iff_isHermitian_ofMatrix_symm,
    ← isSelfAdjoint_iff_isHermitian_ofMatrix_symm]
  simp only [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_conjTranspose]
  exact ⟨fun ⟨h₁₁, h₁₂, _, h₂₂⟩ ↦ ⟨h₁₁, h₁₂, h₂₂⟩,
    fun ⟨h₁₁, h₁₂, h₂₂⟩ ↦ ⟨h₁₁, h₁₂, by simp [← h₁₂], h₂₂⟩⟩

/-- A block-diagonal `CStarMatrix` is self-adjoint iff both diagonal blocks are self-adjoint. -/
@[simp] theorem isSelfAdjoint_fromBlocks_zero₁₂_zero₂₁ [AddMonoid A] [StarAddMonoid A]
    {M : CStarMatrix m m A} {N : CStarMatrix n n A} :
    IsSelfAdjoint (fromBlocks M 0 0 N) ↔ IsSelfAdjoint M ∧ IsSelfAdjoint N := by
  simp [isSelfAdjoint_fromBlocks_iff]

private theorem mem_unitary_iff_ofMatrix_symm {k A : Type*} [Fintype k] [DecidableEq k]
    [Semiring A] [StarRing A] (X : CStarMatrix k k A) :
    X ∈ unitary (CStarMatrix k k A) ↔ ofMatrix.symm X ∈ unitary (Matrix k k A) := by
  simp [Unitary.mem_iff, ← ofMatrix.symm.injective.eq_iff, Matrix.star_eq_conjTranspose]

/-- A block-diagonal `CStarMatrix` is unitary iff both diagonal blocks are unitary. -/
@[simp] theorem fromBlocks_zero₁₂_zero₂₁_mem_unitary [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] [Semiring A] [StarRing A] {M : CStarMatrix m m A} {N : CStarMatrix n n A} :
    fromBlocks M 0 0 N ∈ unitary (CStarMatrix (m ⊕ n) (m ⊕ n) A) ↔
      M ∈ unitary (CStarMatrix m m A) ∧ N ∈ unitary (CStarMatrix n n A) := by
  rw [mem_unitary_iff_ofMatrix_symm, ofMatrix_symm_fromBlocks,
    ← of_zero (m := m) (n := n), ← of_zero (m := n) (n := m), Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Matrix.fromBlocks_zero_zero_mem_unitary,
    mem_unitary_iff_ofMatrix_symm, mem_unitary_iff_ofMatrix_symm]

/-- Reindexing rows and columns by `Equiv.sumCongr` acts blockwise on `fromBlocks`. -/
@[simp] theorem reindexₗ_sumCongr_fromBlocks [Semiring R] [AddCommMonoid A] [Module R A]
    (e₁ : n ≃ p) (e₂ : o ≃ q) (f₁ : l ≃ k) (f₂ : m ≃ r)
    (M₁₁ : CStarMatrix n l A) (M₁₂ : CStarMatrix n m A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o m A) :
    reindexₗ R A (e₁.sumCongr e₂) (f₁.sumCongr f₂) (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (reindexₗ R A e₁ f₁ M₁₁) (reindexₗ R A e₁ f₂ M₁₂)
        (reindexₗ R A e₂ f₁ M₂₁) (reindexₗ R A e₂ f₂ M₂₂) := by
  apply ofMatrix.symm.injective
  have hs₁ : ⇑(e₁.symm.sumCongr e₂.symm) = Sum.map e₁.symm e₂.symm :=
    funext (Equiv.sumCongr_apply _ _)
  have hs₂ : ⇑(f₁.symm.sumCongr f₂.symm) = Sum.map f₁.symm f₂.symm :=
    funext (Equiv.sumCongr_apply _ _)
  simp only [ofMatrix_symm_reindexₗ, ofMatrix_symm_fromBlocks, Matrix.reindex_apply,
    Equiv.sumCongr_symm, hs₁, hs₂, Matrix.fromBlocks_submatrix_sumMap]

/-- Square `reindexₐ` by `Equiv.sumCongr` acts blockwise on `fromBlocks`. -/
@[simp] theorem reindexₐ_sumCongr_fromBlocks [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A] (e₁ : l ≃ n) (e₂ : m ≃ o)
    (M₁₁ : CStarMatrix l l A) (M₁₂ : CStarMatrix l m A)
    (M₂₁ : CStarMatrix m l A) (M₂₂ : CStarMatrix m m A) :
    reindexₐ R A (e₁.sumCongr e₂) (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (reindexₐ R A e₁ M₁₁) (reindexₗ R A e₁ e₂ M₁₂)
        (reindexₗ R A e₂ e₁ M₂₁) (reindexₐ R A e₂ M₂₂) := by
  rw [← reindexₗ_eq_reindexₐ, reindexₗ_sumCongr_fromBlocks, reindexₗ_eq_reindexₐ,
    reindexₗ_eq_reindexₐ]

/-- Reindexing by `Equiv.sumComm` swaps the two diagonal and two off-diagonal blocks. -/
@[simp] theorem reindexₐ_sumComm_fromBlocks [Fintype m] [Fintype n]
    [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A]
    (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix n m A) (M₂₂ : CStarMatrix n n A) :
    reindexₐ R A (Equiv.sumComm m n) (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) = fromBlocks M₂₂ M₂₁ M₁₂ M₁₁ := by
  apply ofMatrix.symm.injective
  rw [← reindexₗ_eq_reindexₐ, ofMatrix_symm_reindexₗ, ofMatrix_symm_fromBlocks,
    ofMatrix_symm_fromBlocks, Matrix.reindex_apply, Equiv.sumComm_symm, Equiv.sumComm_apply,
    Matrix.fromBlocks_submatrix_sum_swap_sum_swap]

/-- Reindexing a nested three-block diagonal matrix by `Equiv.sumAssoc` reassociates the blocks. -/
@[simp] theorem reindexₐ_sumAssoc_fromBlocks [Fintype l] [Fintype m] [Fintype n]
    [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A]
    (L : CStarMatrix l l A) (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    reindexₐ R A (Equiv.sumAssoc l m n) (fromBlocks (fromBlocks L 0 0 M) 0 0 N) =
      fromBlocks L 0 0 (fromBlocks M 0 0 N) := by
  ext (_ | (_ | _)) (_ | (_ | _)) <;> rfl

end FromBlocks

section CornerAndBlockNorm

variable {l m n o R A : Type*}

/-- Block-diagonal inclusion of `CStarMatrix m m A × CStarMatrix n n A` into
`CStarMatrix (m ⊕ n) (m ⊕ n) A` as a non-unital `⋆`-algebra homomorphism. -/
def blockDiagStarAlgHom [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun x := fromBlocks x.1 0 0 x.2
  map_smul' c x := by simp [fromBlocks_smul]
  map_zero' := fromBlocks_zero
  map_add' x y := by simp [fromBlocks_add]
  map_mul' x y := by simp [fromBlocks_multiply]
  map_star' x := by simp [star_fromBlocks]

@[simp] theorem blockDiagStarAlgHom_apply [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (x : CStarMatrix m m A × CStarMatrix n n A) :
    blockDiagStarAlgHom (R := R) x = fromBlocks x.1 0 0 x.2 := (rfl)

theorem blockDiagStarAlgHom_injective [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (blockDiagStarAlgHom (m := m) (n := n) (R := R) (A := A)) := by
  rintro ⟨M₁, N₁⟩ ⟨M₂, N₂⟩ h; simpa [Prod.ext_iff] using h

/-- Upper-left corner embedding `M ↦ fromBlocks M 0 0 0`. -/
def inl [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  blockDiagStarAlgHom.comp (NonUnitalStarAlgHom.inl R _ _)

@[simp] theorem inl_apply [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (M : CStarMatrix m m A) :
    inl (n := n) (R := R) M = fromBlocks M 0 0 0 := (rfl)

/-- Lower-right corner embedding `N ↦ fromBlocks 0 0 0 N`. -/
def inr [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  blockDiagStarAlgHom.comp (NonUnitalStarAlgHom.inr R _ _)

@[simp] theorem inr_apply [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (N : CStarMatrix n n A) :
    inr (m := m) (R := R) N = fromBlocks 0 0 0 N := (rfl)

theorem inl_injective [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (inl (m := m) (n := n) (R := R) (A := A)) := fun _ _ h ↦
  (fromBlocks_inj.mp h).1

theorem inr_injective [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (inr (m := m) (n := n) (R := R) (A := A)) := fun _ _ h ↦
  (fromBlocks_inj.mp h).2.2.2

theorem inl_add_inr [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    inl (n := n) (R := R) M + inr (m := m) (R := R) N = fromBlocks M 0 0 N := by
  simp [fromBlocks_add]

theorem inl_mul_inr [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    inl (n := n) (R := R) M * inr (m := m) (R := R) N = 0 := by simp [fromBlocks_multiply]

theorem inr_mul_inl [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (N : CStarMatrix n n A) (M : CStarMatrix m m A) :
    inr (m := m) (R := R) N * inl (n := n) (R := R) M = 0 := by simp [fromBlocks_multiply]

section MatrixUnitsAndDiagonal

/-- Matrix unit in `CStarMatrix m n A` with entry `a` at `(i, j)` and `0` elsewhere. -/
def single [DecidableEq m] [DecidableEq n] [Zero A] (i : m) (j : n) (a : A) : CStarMatrix m n A :=
  ofMatrix (Matrix.single i j a)

@[simp] theorem ofMatrix_symm_single [DecidableEq m] [DecidableEq n] [Zero A]
    (i : m) (j : n) (a : A) : ofMatrix.symm (single i j a) = Matrix.single i j a := (rfl)

theorem single_apply [DecidableEq m] [DecidableEq n] [Zero A] (i i' : m) (j j' : n) (a : A) :
    single i j a i' j' = if i = i' ∧ j = j' then a else 0 := (rfl)

@[simp] theorem single_apply_same [DecidableEq m] [DecidableEq n] [Zero A]
    (i : m) (j : n) (a : A) : single i j a i j = a := Matrix.single_apply_same i j a

@[simp] theorem single_zero [DecidableEq m] [DecidableEq n] [Zero A] (i : m) (j : n) :
    single i j (0 : A) = 0 := Matrix.single_zero i j

theorem single_add [DecidableEq m] [DecidableEq n] [AddZeroClass A] (i : m) (j : n) (a b : A) :
    single i j (a + b) = single i j a + single i j b := Matrix.single_add i j a b

theorem single_smul [DecidableEq m] [DecidableEq n] [Zero A] [SMulZeroClass R A]
    (i : m) (j : n) (c : R) (a : A) : single i j (c • a) = c • single i j a :=
  (Matrix.smul_single c i j a).symm

@[simp] theorem conjTranspose_single [DecidableEq m] [DecidableEq n] [AddMonoid A] [StarAddMonoid A]
    (i : m) (j : n) (a : A) : (single i j a).conjTranspose = single j i (star a) :=
  Matrix.conjTranspose_single i j a

@[simp] theorem single_mul_single_same [Fintype m] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    [NonUnitalNonAssocSemiring A] (i : l) (j : m) (k : n) (a b : A) :
    single i j a * single j k b = single i k (a * b) := by
  rw [single, single, single, of_mul_of, Matrix.single_mul_single_same]

theorem single_mul_single_of_ne [Fintype m] [DecidableEq l] [DecidableEq m] [DecidableEq n]
    [NonUnitalNonAssocSemiring A] (i : l) {j j' : m} (k : n) (h : j ≠ j') (a b : A) :
    single i j a * single j' k b = 0 := by
  rw [single, single, of_mul_of, Matrix.single_mul_single_of_ne a i j j' h b, of_zero]

/-- Diagonal corner embedding `a ↦ single i i a` into `CStarMatrix n n A`. -/
def singleStarAlgHom [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) :
    A →⋆ₙₐ[R] CStarMatrix n n A where
  toFun a := single i i a
  map_smul' c a := single_smul i i c a
  map_zero' := single_zero i i
  map_add' a b := single_add i i a b
  map_mul' a b := (single_mul_single_same i i i a b).symm
  map_star' a := (conjTranspose_single i i a).symm

@[simp] theorem singleStarAlgHom_apply [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) (a : A) :
    singleStarAlgHom (R := R) i a = single i i a := (rfl)

theorem singleStarAlgHom_injective [Fintype n] [DecidableEq n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (i : n) :
    Function.Injective (singleStarAlgHom (R := R) (A := A) i) := fun a b h ↦ by
  simpa using congrArg (fun M : CStarMatrix n n A ↦ M i i) h

@[simp] theorem fromBlocks_diagonal [DecidableEq l] [DecidableEq m] [Zero A]
    (d₁ : l → A) (d₂ : m → A) :
    fromBlocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal (Sum.elim d₁ d₂) := by
  apply ofMatrix.symm.injective
  rw [ofMatrix_symm_fromBlocks, ofMatrix_symm_diagonal, ofMatrix_symm_diagonal,
    ofMatrix_symm_diagonal, ← of_zero (m := l) (n := m), ← of_zero (m := m) (n := l),
    Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_diagonal]

end MatrixUnitsAndDiagonal

section Norm

variable [Fintype l] [Fintype m] [Fintype n] [Fintype o]
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The operator norm of a block-diagonal `CStarMatrix` (even with rectangular blocks) is the
maximum of the operator norms of its diagonal blocks. -/
@[simp] theorem norm_fromBlocks_zero₁₂_zero₂₁ (M : CStarMatrix n l A) (N : CStarMatrix o m A) :
    ‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖ := by
  have hsq (P : CStarMatrix l l A) (Q : CStarMatrix m m A) :
      ‖fromBlocks P 0 0 Q‖ = max ‖P‖ ‖Q‖ := by
    simpa [Prod.norm_def] using
      NonUnitalStarAlgHom.norm_map (blockDiagStarAlgHom (R := ℂ) (A := A))
        blockDiagStarAlgHom_injective (P, Q)
  rw [← sq_eq_sq₀ (norm_nonneg _) (le_max_iff.mpr (.inl (norm_nonneg M))),
    ← norm_conjTranspose_mul_self]
  simp only [fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply,
    CStarMatrix.mul_zero, CStarMatrix.zero_mul, add_zero, zero_add]
  rw [hsq, norm_conjTranspose_mul_self, norm_conjTranspose_mul_self,
    max_pow_of_nonneg (norm_nonneg M) (norm_nonneg N) 2]

/-- The operator norm of an anti-diagonal `2 × 2` block `CStarMatrix` is the maximum of the
operator norms of its off-diagonal blocks. -/
@[simp] theorem norm_fromBlocks_zero₁₁_zero₂₂ (M : CStarMatrix n m A) (N : CStarMatrix o l A) :
    ‖fromBlocks 0 M N 0‖ = max ‖M‖ ‖N‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (le_max_iff.mpr (.inl (norm_nonneg M))),
    ← norm_conjTranspose_mul_self]
  simp only [fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply,
    CStarMatrix.mul_zero, CStarMatrix.zero_mul, add_zero, zero_add]
  rw [norm_fromBlocks_zero₁₂_zero₂₁, norm_conjTranspose_mul_self, norm_conjTranspose_mul_self,
    max_comm, max_pow_of_nonneg (norm_nonneg M) (norm_nonneg N) 2]

/-- The upper-left corner embedding `inl` preserves operator norms. -/
theorem norm_inl [Semiring R] [Module R A] (M : CStarMatrix m m A) :
    ‖inl (n := n) (R := R) M‖ = ‖M‖ := by simp

/-- The lower-right corner embedding `inr` preserves operator norms. -/
theorem norm_inr [Semiring R] [Module R A] (N : CStarMatrix n n A) :
    ‖inr (m := m) (R := R) N‖ = ‖N‖ := by simp

/-- The upper-left corner embedding `inl` is an isometry. -/
theorem isometry_inl [Semiring R] [Module R A] :
    Isometry (inl (m := m) (n := n) (R := R) (A := A)) :=
  AddMonoidHomClass.isometry_of_norm _ norm_inl

/-- The lower-right corner embedding `inr` is an isometry. -/
theorem isometry_inr [Semiring R] [Module R A] :
    Isometry (inr (m := m) (n := n) (R := R) (A := A)) :=
  AddMonoidHomClass.isometry_of_norm _ norm_inr

/-- Every matrix unit `single i j a` in a rectangular `CStarMatrix` has norm `‖a‖`. -/
@[simp] theorem norm_single [DecidableEq m] [DecidableEq n] (i : m) (j : n) (a : A) :
    ‖single i j a‖ = ‖a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_conjTranspose_mul_self,
    conjTranspose_single, single_mul_single_same, ← singleStarAlgHom_apply (R := ℂ),
    NonUnitalStarAlgHom.norm_map (singleStarAlgHom (R := ℂ) (A := A) j)
      (singleStarAlgHom_injective j),
    CStarRing.norm_star_mul_self, sq]

/-- The diagonal corner embedding `singleStarAlgHom i` preserves norms. -/
theorem norm_singleStarAlgHom [DecidableEq n] [Semiring R] [Module R A] (i : n) (a : A) :
    ‖singleStarAlgHom (R := R) i a‖ = ‖a‖ :=
  norm_single i i a

/-- The diagonal corner embedding `singleStarAlgHom i` is an isometry. -/
theorem isometry_singleStarAlgHom [DecidableEq n] [Semiring R] [Module R A] (i : n) :
    Isometry (singleStarAlgHom (R := R) (A := A) i) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_singleStarAlgHom i)

/-- The operator norm of `diagonal d` equals `‖d‖` (`supᵢ ‖d i‖`). -/
@[simp] theorem norm_diagonal [DecidableEq n] (d : n → A) : ‖diagonal d‖ = ‖d‖ := by
  rw [← diagonalStarAlgHom_apply (R := ℂ)]
  exact NonUnitalStarAlgHom.norm_map (diagonalStarAlgHom (R := ℂ)) diagonalStarAlgHom_injective d

end Norm

end CornerAndBlockNorm

end CStarMatrix
