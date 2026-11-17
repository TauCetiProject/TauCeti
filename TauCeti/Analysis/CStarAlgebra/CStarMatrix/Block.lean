/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Block matrices, corner inclusions, and block-diagonal operator norms on `CStarMatrix`

This file develops `2 × 2` block matrices `CStarMatrix.fromBlocks`, block-diagonal and corner
`⋆`-algebra homomorphisms, sum-reindexing laws, and the block-diagonal operator-norm formula
`‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖` over possibly non-unital C⋆-algebras.

## Main definitions

* `CStarMatrix.fromBlocks`: `2 × 2` block matrices in `CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A`.
* `CStarMatrix.fromBlocksDiagonalₙₐ`, `CStarMatrix.inlₙₐ`, `CStarMatrix.inrₙₐ`: the
  block-diagonal sum `x ↦ fromBlocks x.1 0 0 x.2` and upper-left / lower-right corner embeddings
  as non-unital `⋆`-algebra homomorphisms.

## Main results

* `CStarMatrix.isStarProjection_fromBlocks_zero`: `fromBlocks p 0 0 q` is a star projection iff
  `p` and `q` are star projections.
* `CStarMatrix.reindexₗ_sumComm_fromBlocks`, `CStarMatrix.reindexₐ_sumComm_fromBlocks`,
  `CStarMatrix.reindexₗ_sumAssoc_fromBlocks_zero`, `CStarMatrix.reindexₐ_sumAssoc_fromBlocks_zero`:
  reindexing `2 × 2` and nested block matrices by `Equiv.sumComm` and `Equiv.sumAssoc`.
* `CStarMatrix.norm_fromBlocks_zero`: `‖fromBlocks M 0 0 N‖ = max ‖M‖ ‖N‖` for rectangular
  matrices `M` and `N`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., MSRI Publications 5, Cambridge
  University Press (1998), Chapter III, §4.6.
* M. Rørdam, F. Larsen, N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, LMS Student
  Texts 49, Cambridge University Press (2000), Chapter 2.
-/

public section

namespace CStarMatrix

section Blocks

variable {m₁ m₂ m₃ n₁ n₂ n₃ o₁ o₂ R A B : Type*}

/-- Assemble four `CStarMatrix` blocks into a `(m₁ ⊕ m₂) × (n₁ ⊕ n₂)` matrix. -/
def fromBlocks (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) :
    CStarMatrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
    (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂))

@[simp]
theorem ofMatrix_symm_fromBlocks (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) :
    ofMatrix.symm (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
        (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂) := (rfl)

@[simp]
theorem ofMatrix_fromBlocks (M₁₁ : Matrix m₁ n₁ A) (M₁₂ : Matrix m₁ n₂ A)
    (M₂₁ : Matrix m₂ n₁ A) (M₂₂ : Matrix m₂ n₂ A) :
    ofMatrix (Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (ofMatrix M₁₁) (ofMatrix M₁₂) (ofMatrix M₂₁) (ofMatrix M₂₂) := (rfl)

@[simp]
theorem fromBlocks_apply₁₁ (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) (i : m₁) (j : n₁) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (.inl i) (.inl j) = M₁₁ i j := (rfl)

@[simp]
theorem fromBlocks_apply₁₂ (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) (i : m₁) (j : n₂) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (.inl i) (.inr j) = M₁₂ i j := (rfl)

@[simp]
theorem fromBlocks_apply₂₁ (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) (i : m₂) (j : n₁) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (.inr i) (.inl j) = M₂₁ i j := (rfl)

@[simp]
theorem fromBlocks_apply₂₂ (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) (i : m₂) (j : n₂) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (.inr i) (.inr j) = M₂₂ i j := (rfl)

@[simp]
theorem fromBlocks_inj {M₁₁ N₁₁ : CStarMatrix m₁ n₁ A} {M₁₂ N₁₂ : CStarMatrix m₁ n₂ A}
    {M₂₁ N₂₁ : CStarMatrix m₂ n₁ A} {M₂₂ N₂₂ : CStarMatrix m₂ n₂ A} :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ ↔
      M₁₁ = N₁₁ ∧ M₁₂ = N₁₂ ∧ M₂₁ = N₂₁ ∧ M₂₂ = N₂₂ := by
  rw [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_fromBlocks, ofMatrix_symm_fromBlocks,
    Matrix.fromBlocks_inj]
  simp [ofMatrix.symm.injective.eq_iff]

@[simp]
theorem fromBlocks_zero [Zero A] :
    fromBlocks (0 : CStarMatrix m₁ n₁ A) (0 : CStarMatrix m₁ n₂ A)
      (0 : CStarMatrix m₂ n₁ A) (0 : CStarMatrix m₂ n₂ A) = 0 :=
  ofMatrix.symm.injective Matrix.fromBlocks_zero

@[simp]
theorem fromBlocks_add [Add A]
    (M₁₁ N₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ N₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ N₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ N₂₂ : CStarMatrix m₂ n₂ A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ + fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ + N₁₁) (M₁₂ + N₁₂) (M₂₁ + N₂₁) (M₂₂ + N₂₂) :=
  ofMatrix.symm.injective <| Matrix.fromBlocks_add _ _ _ _ _ _ _ _

@[simp]
theorem fromBlocks_neg [Neg A]
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) :
    -fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks (-M₁₁) (-M₁₂) (-M₂₁) (-M₂₂) :=
  ofMatrix.symm.injective <| Matrix.fromBlocks_neg _ _ _ _

@[simp]
theorem fromBlocks_sub [Sub A]
    (M₁₁ N₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ N₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ N₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ N₂₂ : CStarMatrix m₂ n₂ A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ - fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ - N₁₁) (M₁₂ - N₁₂) (M₂₁ - N₂₁) (M₂₂ - N₂₂) := by
  ext (i | i) (j | j) <;> simp

@[simp]
theorem fromBlocks_smul [SMul R A] (r : R)
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) :
    r • fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks (r • M₁₁) (r • M₁₂) (r • M₂₁) (r • M₂₂) :=
  ofMatrix.symm.injective <| Matrix.fromBlocks_smul r _ _ _ _

@[simp]
theorem fromBlocks_conjTranspose [Star A]
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).conjTranspose =
      fromBlocks M₁₁.conjTranspose M₂₁.conjTranspose M₁₂.conjTranspose M₂₂.conjTranspose :=
  ofMatrix.symm.injective <| Matrix.fromBlocks_conjTranspose _ _ _ _

@[simp]
theorem fromBlocks_star [Star A]
    (M₁₁ : CStarMatrix n₁ n₁ A) (M₁₂ : CStarMatrix n₁ n₂ A)
    (M₂₁ : CStarMatrix n₂ n₁ A) (M₂₂ : CStarMatrix n₂ n₂ A) :
    star (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (star M₁₁) M₂₁.conjTranspose M₁₂.conjTranspose (star M₂₂) :=
  fromBlocks_conjTranspose M₁₁ M₁₂ M₂₁ M₂₂

theorem fromBlocks_multiply [Fintype n₁] [Fintype n₂] [NonUnitalNonAssocSemiring A]
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A)
    (N₁₁ : CStarMatrix n₁ o₁ A) (N₁₂ : CStarMatrix n₁ o₂ A)
    (N₂₁ : CStarMatrix n₂ o₁ A) (N₂₂ : CStarMatrix n₂ o₂ A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ * N₁₁ + M₁₂ * N₂₁) (M₁₁ * N₁₂ + M₁₂ * N₂₂)
        (M₂₁ * N₁₁ + M₂₂ * N₂₁) (M₂₁ * N₁₂ + M₂₂ * N₂₂) :=
  ofMatrix.symm.injective <| Matrix.fromBlocks_multiply _ _ _ _ _ _ _ _

@[simp]
theorem fromBlocks_one [DecidableEq n₁] [DecidableEq n₂] [Zero A] [One A] :
    fromBlocks (1 : CStarMatrix n₁ n₁ A) 0 0 (1 : CStarMatrix n₂ n₂ A) = 1 :=
  ofMatrix.symm.injective Matrix.fromBlocks_one

@[simp]
theorem fromBlocks_map
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) (f : A → B) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).map f =
      fromBlocks (M₁₁.map f) (M₁₂.map f) (M₂₁.map f) (M₂₂.map f) :=
  ofMatrix.symm.injective <| Matrix.fromBlocks_map _ _ _ _ f

/-- Entrywise amplification `mapₙₐ` distributes over `fromBlocks`. -/
theorem mapₙₐ_fromBlocks [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (f : A →⋆ₙₐ[R] B)
    (M₁₁ : CStarMatrix n₁ n₁ A) (M₁₂ : CStarMatrix n₁ n₂ A)
    (M₂₁ : CStarMatrix n₂ n₁ A) (M₂₂ : CStarMatrix n₂ n₂ A) :
    mapₙₐ f (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (mapₙₐ f M₁₁) (M₁₂.map f) (M₂₁.map f) (mapₙₐ f M₂₂) :=
  fromBlocks_map M₁₁ M₁₂ M₂₁ M₂₂ f

@[simp]
theorem isStarProjection_fromBlocks_zero [Fintype n₁] [Fintype n₂]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    {p : CStarMatrix n₁ n₁ A} {q : CStarMatrix n₂ n₂ A} :
    IsStarProjection (fromBlocks p 0 0 q) ↔ IsStarProjection p ∧ IsStarProjection q := by
  simp only [isStarProjection_iff, IsIdempotentElem, IsSelfAdjoint, fromBlocks_multiply,
    fromBlocks_star, CStarMatrix.mul_zero, CStarMatrix.zero_mul, add_zero, zero_add,
    conjTranspose_zero, fromBlocks_inj, true_and]
  tauto

/-- Reindexing `fromBlocks M₁₁ M₁₂ M₂₁ M₂₂` by `Equiv.sumComm` yields
`fromBlocks M₂₂ M₂₁ M₁₂ M₁₁`. -/
@[simp]
theorem reindexₗ_sumComm_fromBlocks [Semiring R] [AddCommMonoid A] [Module R A]
    (M₁₁ : CStarMatrix m₁ n₁ A) (M₁₂ : CStarMatrix m₁ n₂ A)
    (M₂₁ : CStarMatrix m₂ n₁ A) (M₂₂ : CStarMatrix m₂ n₂ A) :
    reindexₗ R A (Equiv.sumComm m₁ m₂) (Equiv.sumComm n₁ n₂) (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks M₂₂ M₂₁ M₁₂ M₁₁ :=
  ofMatrix.symm.injective <| by
    rw [ofMatrix_symm_reindexₗ]
    ext (i | i) (j | j) <;> simp

/-- Reindexing a square `2 × 2` block matrix by `Equiv.sumComm` via `reindexₐ` swaps both diagonal
and off-diagonal blocks. -/
@[simp]
theorem reindexₐ_sumComm_fromBlocks [Fintype n₁] [Fintype n₂] [Semiring R] [AddCommMonoid A]
    [Mul A] [Module R A] [Star A]
    (M₁₁ : CStarMatrix n₁ n₁ A) (M₁₂ : CStarMatrix n₁ n₂ A)
    (M₂₁ : CStarMatrix n₂ n₁ A) (M₂₂ : CStarMatrix n₂ n₂ A) :
    reindexₐ R A (Equiv.sumComm n₁ n₂) (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks M₂₂ M₂₁ M₁₂ M₁₁ := by
  rw [reindexₐ_eq_reindexₗ, reindexₗ_sumComm_fromBlocks]

/-- Reindexing nested block-diagonal sums by `Equiv.sumAssoc` reassociates the blocks. -/
@[simp]
theorem reindexₗ_sumAssoc_fromBlocks_zero
    [Semiring R] [AddCommMonoid A] [Module R A]
    (L : CStarMatrix m₁ n₁ A) (M : CStarMatrix m₂ n₂ A) (N : CStarMatrix m₃ n₃ A) :
    reindexₗ R A (Equiv.sumAssoc m₁ m₂ m₃) (Equiv.sumAssoc n₁ n₂ n₃)
        (fromBlocks (fromBlocks L 0 0 M) 0 0 N) =
      fromBlocks L 0 0 (fromBlocks M 0 0 N) :=
  ofMatrix.symm.injective <| by
    rw [ofMatrix_symm_reindexₗ]
    ext (i | (i | i)) (j | (j | j)) <;> simp

/-- Reindexing nested square block-diagonal sums by `Equiv.sumAssoc` via `reindexₐ` reassociates
the blocks. -/
@[simp]
theorem reindexₐ_sumAssoc_fromBlocks_zero [Fintype n₁] [Fintype n₂] [Fintype n₃]
    [Semiring R] [AddCommMonoid A] [Mul A] [Module R A] [Star A]
    (L : CStarMatrix n₁ n₁ A) (M : CStarMatrix n₂ n₂ A) (N : CStarMatrix n₃ n₃ A) :
    reindexₐ R A (Equiv.sumAssoc n₁ n₂ n₃) (fromBlocks (fromBlocks L 0 0 M) 0 0 N) =
      fromBlocks L 0 0 (fromBlocks M 0 0 N) := by
  rw [reindexₐ_eq_reindexₗ, reindexₗ_sumAssoc_fromBlocks_zero]

/-- Block-diagonal sum `x ↦ fromBlocks x.1 0 0 x.2` as a non-unital `⋆`-algebra homomorphism
`CStarMatrix n₁ n₁ A × CStarMatrix n₂ n₂ A →⋆ₙₐ[R] CStarMatrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) A`. -/
def fromBlocksDiagonalₙₐ (R A : Type*) [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n₁ n₁ A × CStarMatrix n₂ n₂ A →⋆ₙₐ[R] CStarMatrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) A where
  toFun x := fromBlocks x.1 0 0 x.2
  map_smul' r x := by simp [smul_zero]
  map_zero' := fromBlocks_zero
  map_add' x y := by simp
  map_mul' x y := by simp [fromBlocks_multiply]
  map_star' x := by simp

@[simp]
theorem fromBlocksDiagonalₙₐ_apply [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (x : CStarMatrix n₁ n₁ A × CStarMatrix n₂ n₂ A) :
    fromBlocksDiagonalₙₐ R A x = fromBlocks x.1 0 0 x.2 := (rfl)

theorem fromBlocksDiagonalₙₐ_injective [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (fromBlocksDiagonalₙₐ (n₁ := n₁) (n₂ := n₂) R A) := by
  rintro ⟨M₁, M₂⟩ ⟨N₁, N₂⟩ h
  obtain ⟨rfl, -, -, rfl⟩ := fromBlocks_inj.mp h
  rfl

/-- Upper-left corner inclusion `M ↦ fromBlocks M 0 0 0` as a non-unital `⋆`-homomorphism. -/
def inlₙₐ (R A : Type*) (n₂ : Type*) [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n₁ n₁ A →⋆ₙₐ[R] CStarMatrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) A :=
  (fromBlocksDiagonalₙₐ R A).comp (.inl R (CStarMatrix n₁ n₁ A) (CStarMatrix n₂ n₂ A))

@[simp]
theorem inlₙₐ_apply [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (M : CStarMatrix n₁ n₁ A) :
    inlₙₐ R A n₂ M = fromBlocks M 0 0 0 := (rfl)

theorem inlₙₐ_injective [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (inlₙₐ (n₁ := n₁) R A n₂) :=
  fun _ _ h => (fromBlocks_inj.mp h).1

/-- Lower-right corner inclusion `N ↦ fromBlocks 0 0 0 N` as a non-unital `⋆`-homomorphism. -/
def inrₙₐ (R A : Type*) (n₁ : Type*) [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n₂ n₂ A →⋆ₙₐ[R] CStarMatrix (n₁ ⊕ n₂) (n₁ ⊕ n₂) A :=
  (fromBlocksDiagonalₙₐ R A).comp (.inr R (CStarMatrix n₁ n₁ A) (CStarMatrix n₂ n₂ A))

@[simp]
theorem inrₙₐ_apply [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (N : CStarMatrix n₂ n₂ A) :
    inrₙₐ R A n₁ N = fromBlocks 0 0 0 N := (rfl)

theorem inrₙₐ_injective [Fintype n₁] [Fintype n₂] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (inrₙₐ (n₂ := n₂) R A n₁) :=
  fun _ _ h => (fromBlocks_inj.mp h).2.2.2

end Blocks

section BlockNorm

variable {m₁ m₂ n₁ n₂ A : Type*}
  [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

private theorem norm_fromBlocks_zero_sq [Fintype n₁] [Fintype n₂]
    (X : CStarMatrix n₁ n₁ A) (Y : CStarMatrix n₂ n₂ A) :
    ‖fromBlocks X (0 : CStarMatrix n₁ n₂ A) (0 : CStarMatrix n₂ n₁ A) Y‖ = max ‖X‖ ‖Y‖ := by
  simpa [Prod.norm_def] using
    NonUnitalStarAlgHom.norm_map (fromBlocksDiagonalₙₐ ℂ A) fromBlocksDiagonalₙₐ_injective (X, Y)

/-- The operator norm of a block-diagonal `CStarMatrix` is the maximum of the norms of its
diagonal blocks. -/
@[simp]
theorem norm_fromBlocks_zero [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂]
    (M : CStarMatrix m₁ n₁ A) (N : CStarMatrix m₂ n₂ A) :
    ‖fromBlocks M (0 : CStarMatrix m₁ n₂ A) (0 : CStarMatrix m₂ n₁ A) N‖ = max ‖M‖ ‖N‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (le_max_iff.mpr (.inl (norm_nonneg M))),
    ← norm_conjTranspose_mul_self]
  simp only [fromBlocks_conjTranspose, conjTranspose_zero, fromBlocks_multiply,
    CStarMatrix.mul_zero, CStarMatrix.zero_mul, add_zero, zero_add]
  rw [norm_fromBlocks_zero_sq, norm_conjTranspose_mul_self, norm_conjTranspose_mul_self]
  rcases le_total ‖M‖ ‖N‖ with h | h
  · rw [max_eq_right h, max_eq_right ((sq_le_sq₀ (norm_nonneg M) (norm_nonneg N)).mpr h)]
  · rw [max_eq_left h, max_eq_left ((sq_le_sq₀ (norm_nonneg N) (norm_nonneg M)).mpr h)]

end BlockNorm

end CStarMatrix
