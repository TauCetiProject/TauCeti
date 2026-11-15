/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Block calculus, amplification, and operator norms for `CStarMatrix`

Forming direct sums of matrix projections, comparing orthogonal sums `p₁ + p₂` with `p₁ ⊕ p₂`, and
stabilizing rectangular partial isometries to unitaries and projection paths require rectangular
block operations on `CStarMatrix m n A` over a (possibly non-unital) C⋆-algebra `A`:

* Four-block matrices `CStarMatrix.fromBlocks` and block-extraction eliminators
  `CStarMatrix.toBlocks₁₁`, `CStarMatrix.toBlocks₁₂`, `CStarMatrix.toBlocks₂₁`, and
  `CStarMatrix.toBlocks₂₂`.
* Vertical row stacks `CStarMatrix.fromRows` and block-diagonal direct sums `CStarMatrix.blockSum`,
  with bundled `⋆`-homomorphisms (`blockSumNonUnitalStarAlgHom`, `inlNonUnitalStarAlgHom`,
  `inrNonUnitalStarAlgHom`).
* Finite block-diagonal amplification `CStarMatrix.amplify` (`1_k ⊗ M`), bundled as
  `amplifyNonUnitalStarAlgHom` and `amplifyStarAlgHom`.
* Exact rectangular operator norms and `@[fun_prop]` continuity: `‖blockSum M N‖ = max ‖M‖ ‖N‖`
  and, when `[Nonempty k]`, `‖amplify k M‖ = ‖M‖`.

## Main declarations

* `CStarMatrix.fromBlocks`, `CStarMatrix.toBlocks₁₁`, `CStarMatrix.toBlocks₁₂`,
  `CStarMatrix.toBlocks₂₁`, `CStarMatrix.toBlocks₂₂`, `CStarMatrix.fromRows`,
  `CStarMatrix.blockSum`, `CStarMatrix.amplify`.
* `CStarMatrix.blockSumNonUnitalStarAlgHom`, `CStarMatrix.inlNonUnitalStarAlgHom`,
  `CStarMatrix.inrNonUnitalStarAlgHom`, `CStarMatrix.amplifyNonUnitalStarAlgHom`,
  `CStarMatrix.amplifyStarAlgHom`.
* `CStarMatrix.norm_blockSum`, `CStarMatrix.norm_amplify`, `CStarMatrix.continuous_fromBlocks`,
  `CStarMatrix.continuous_blockSum`, `CStarMatrix.continuous_amplify`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §4.6 and §5.1.
* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 4.
-/

public section

open scoped Matrix ComplexOrder

namespace CStarMatrix

section Blocks
variable {k l m n o p m₁ m₂ m₃ n₁ n₂ n₃ R A B : Type*}

/-- Build a four-block `CStarMatrix` from blocks of sizes `m × l`, `m × n`, `o × l`, and `o × n`. -/
def fromBlocks (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) : CStarMatrix (m ⊕ o) (l ⊕ n) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
    (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂))

@[simp] theorem ofMatrix_symm_fromBlocks (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    ofMatrix.symm (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) = Matrix.fromBlocks (ofMatrix.symm M₁₁)
      (ofMatrix.symm M₁₂) (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂) := (rfl)
@[simp] theorem of_fromBlocks (M₁₁ : Matrix m l A) (M₁₂ : Matrix m n A)
    (M₂₁ : Matrix o l A) (M₂₂ : Matrix o n A) : ofMatrix (Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (ofMatrix M₁₁) (ofMatrix M₁₂) (ofMatrix M₂₁) (ofMatrix M₂₂) := (rfl)

/-- Extract the upper-left `m × l` block of `M : CStarMatrix (m ⊕ o) (l ⊕ n) A`. -/
def toBlocks₁₁ (M : CStarMatrix (m ⊕ o) (l ⊕ n) A) : CStarMatrix m l A :=
  ofMatrix (ofMatrix.symm M).toBlocks₁₁

/-- Extract the upper-right `m × n` block of `M : CStarMatrix (m ⊕ o) (l ⊕ n) A`. -/
def toBlocks₁₂ (M : CStarMatrix (m ⊕ o) (l ⊕ n) A) : CStarMatrix m n A :=
  ofMatrix (ofMatrix.symm M).toBlocks₁₂

/-- Extract the lower-left `o × l` block of `M : CStarMatrix (m ⊕ o) (l ⊕ n) A`. -/
def toBlocks₂₁ (M : CStarMatrix (m ⊕ o) (l ⊕ n) A) : CStarMatrix o l A :=
  ofMatrix (ofMatrix.symm M).toBlocks₂₁

/-- Extract the lower-right `o × n` block of `M : CStarMatrix (m ⊕ o) (l ⊕ n) A`. -/
def toBlocks₂₂ (M : CStarMatrix (m ⊕ o) (l ⊕ n) A) : CStarMatrix o n A :=
  ofMatrix (ofMatrix.symm M).toBlocks₂₂

@[simp] theorem ofMatrix_symm_toBlocks₁₁ (M : CStarMatrix (m ⊕ o) (l ⊕ n) A) :
    ofMatrix.symm M.toBlocks₁₁ = (ofMatrix.symm M).toBlocks₁₁ := (rfl)
@[simp] theorem ofMatrix_symm_toBlocks₁₂ (M : CStarMatrix (m ⊕ o) (l ⊕ n) A) :
    ofMatrix.symm M.toBlocks₁₂ = (ofMatrix.symm M).toBlocks₁₂ := (rfl)
@[simp] theorem ofMatrix_symm_toBlocks₂₁ (M : CStarMatrix (m ⊕ o) (l ⊕ n) A) :
    ofMatrix.symm M.toBlocks₂₁ = (ofMatrix.symm M).toBlocks₂₁ := (rfl)
@[simp] theorem ofMatrix_symm_toBlocks₂₂ (M : CStarMatrix (m ⊕ o) (l ⊕ n) A) :
    ofMatrix.symm M.toBlocks₂₂ = (ofMatrix.symm M).toBlocks₂₂ := (rfl)
@[simp] theorem toBlocks₁₁_apply (M : CStarMatrix (m ⊕ o) (l ⊕ n) A) (i : m) (j : l) :
    M.toBlocks₁₁ i j = M (Sum.inl i) (Sum.inl j) := (rfl)
@[simp] theorem toBlocks₁₂_apply (M : CStarMatrix (m ⊕ o) (l ⊕ n) A) (i : m) (j : n) :
    M.toBlocks₁₂ i j = M (Sum.inl i) (Sum.inr j) := (rfl)
@[simp] theorem toBlocks₂₁_apply (M : CStarMatrix (m ⊕ o) (l ⊕ n) A) (i : o) (j : l) :
    M.toBlocks₂₁ i j = M (Sum.inr i) (Sum.inl j) := (rfl)
@[simp] theorem toBlocks₂₂_apply (M : CStarMatrix (m ⊕ o) (l ⊕ n) A) (i : o) (j : n) :
    M.toBlocks₂₂ i j = M (Sum.inr i) (Sum.inr j) := (rfl)

/-- Reassembling the four extracted blocks of `M` recovers `M`. -/
theorem fromBlocks_toBlocks (M : CStarMatrix (m ⊕ o) (l ⊕ n) A) :
    fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = M :=
  ofMatrix.symm.injective (Matrix.fromBlocks_toBlocks (ofMatrix.symm M))

@[simp] theorem toBlocks_fromBlocks₁₁ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).toBlocks₁₁ = M₁₁ := (rfl)
@[simp] theorem toBlocks_fromBlocks₁₂ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).toBlocks₁₂ = M₁₂ := (rfl)
@[simp] theorem toBlocks_fromBlocks₂₁ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).toBlocks₂₁ = M₂₁ := (rfl)
@[simp] theorem toBlocks_fromBlocks₂₂ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).toBlocks₂₂ = M₂₂ := (rfl)
@[simp] theorem fromBlocks_apply₁₁ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) (i : m) (j : l) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inl j) = M₁₁ i j := (rfl)
@[simp] theorem fromBlocks_apply₁₂ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) (i : m) (j : n) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inl i) (Sum.inr j) = M₁₂ i j := (rfl)
@[simp] theorem fromBlocks_apply₂₁ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) (i : o) (j : l) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inl j) = M₂₁ i j := (rfl)
@[simp] theorem fromBlocks_apply₂₂ (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) (i : o) (j : n) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (Sum.inr i) (Sum.inr j) = M₂₂ i j := (rfl)
@[simp] theorem fromBlocks_inj {M₁₁ N₁₁ : CStarMatrix m l A} {M₁₂ N₁₂ : CStarMatrix m n A}
    {M₂₁ N₂₁ : CStarMatrix o l A} {M₂₂ N₂₂ : CStarMatrix o n A} :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ ↔
      M₁₁ = N₁₁ ∧ M₁₂ = N₁₂ ∧ M₂₁ = N₂₁ ∧ M₂₂ = N₂₂ := by
  rw [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_fromBlocks, ofMatrix_symm_fromBlocks,
    Matrix.fromBlocks_inj]; simp [ofMatrix.symm.injective.eq_iff]
@[simp] theorem fromBlocks_zero [Zero A] : fromBlocks (0 : CStarMatrix m l A)
    (0 : CStarMatrix m n A) (0 : CStarMatrix o l A) (0 : CStarMatrix o n A) = 0 :=
  ofMatrix.symm.injective Matrix.fromBlocks_zero
@[simp] theorem fromBlocks_eq_zero_iff [Zero A] {M₁₁ : CStarMatrix m l A} {M₁₂ : CStarMatrix m n A}
    {M₂₁ : CStarMatrix o l A} {M₂₂ : CStarMatrix o n A} :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = 0 ↔ M₁₁ = 0 ∧ M₁₂ = 0 ∧ M₂₁ = 0 ∧ M₂₂ = 0 := by
  rw [← fromBlocks_zero, fromBlocks_inj]
@[simp] theorem fromBlocks_one [DecidableEq l] [DecidableEq m] [Zero A] [One A] :
    fromBlocks (1 : CStarMatrix l l A) 0 0 (1 : CStarMatrix m m A) = 1 :=
  ofMatrix.symm.injective Matrix.fromBlocks_one
@[simp] theorem fromBlocks_add [Add A] (M₁₁ N₁₁ : CStarMatrix m l A) (M₁₂ N₁₂ : CStarMatrix m n A)
    (M₂₁ N₂₁ : CStarMatrix o l A) (M₂₂ N₂₂ : CStarMatrix o n A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ + fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ + N₁₁) (M₁₂ + N₁₂) (M₂₁ + N₂₁) (M₂₂ + N₂₂) :=
  ofMatrix.symm.injective (Matrix.fromBlocks_add _ _ _ _ _ _ _ _)
@[simp] theorem fromBlocks_neg [Neg A] (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    -fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks (-M₁₁) (-M₁₂) (-M₂₁) (-M₂₂) :=
  ofMatrix.symm.injective (Matrix.fromBlocks_neg _ _ _ _)
@[simp] theorem fromBlocks_sub [AddGroup A] (M₁₁ N₁₁ : CStarMatrix m l A)
    (M₁₂ N₁₂ : CStarMatrix m n A) (M₂₁ N₂₁ : CStarMatrix o l A) (M₂₂ N₂₂ : CStarMatrix o n A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ - fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ - N₁₁) (M₁₂ - N₁₂) (M₂₁ - N₂₁) (M₂₂ - N₂₂) := by ext (_ | _) (_ | _) <;> rfl
@[simp] theorem fromBlocks_smul [SMul R A] (r : R) (M₁₁ : CStarMatrix m l A)
    (M₁₂ : CStarMatrix m n A) (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    r • fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks (r • M₁₁) (r • M₁₂) (r • M₂₁) (r • M₂₂) :=
  ofMatrix.symm.injective (Matrix.fromBlocks_smul r _ _ _ _)

/-- Block-by-block multiplication of `CStarMatrix.fromBlocks`. -/
theorem fromBlocks_mul [Fintype l] [Fintype n] [NonUnitalNonAssocSemiring A]
    (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A) (M₂₁ : CStarMatrix o l A)
    (M₂₂ : CStarMatrix o n A) (N₁₁ : CStarMatrix l k A) (N₁₂ : CStarMatrix l p A)
    (N₂₁ : CStarMatrix n k A) (N₂₂ : CStarMatrix n p A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ * N₁₁ + M₁₂ * N₂₁) (M₁₁ * N₁₂ + M₁₂ * N₂₂)
        (M₂₁ * N₁₁ + M₂₂ * N₂₁) (M₂₁ * N₁₂ + M₂₂ * N₂₂) :=
  ofMatrix.symm.injective (Matrix.fromBlocks_multiply _ _ _ _ _ _ _ _)

/-- Conjugate transpose of a four-block `CStarMatrix`. -/
@[simp] theorem fromBlocks_conjTranspose [Star A] (M₁₁ : CStarMatrix m l A)
    (M₁₂ : CStarMatrix m n A) (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).conjTranspose =
      fromBlocks M₁₁.conjTranspose M₂₁.conjTranspose M₁₂.conjTranspose M₂₂.conjTranspose :=
  ofMatrix.symm.injective (Matrix.fromBlocks_conjTranspose _ _ _ _)

/-- `star` of a square four-block `CStarMatrix`. -/
@[simp] theorem star_fromBlocks [Star A] (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix n m A) (M₂₂ : CStarMatrix n n A) : star (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (star M₁₁) M₂₁.conjTranspose M₁₂.conjTranspose (star M₂₂) :=
  fromBlocks_conjTranspose M₁₁ M₁₂ M₂₁ M₂₂
@[simp] theorem map_fromBlocks (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) (f : A → B) :
    (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).map f =
      fromBlocks (M₁₁.map f) (M₁₂.map f) (M₂₁.map f) (M₂₂.map f) :=
  ofMatrix.symm.injective (Matrix.fromBlocks_map _ _ _ _ f)

/-- Stack matrices of sizes `m × l` and `o × l` vertically into a `(m ⊕ o) × l` `CStarMatrix`. -/
def fromRows (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A) : CStarMatrix (m ⊕ o) l A :=
  ofMatrix (Matrix.fromRows (ofMatrix.symm M₁) (ofMatrix.symm M₂))

@[simp] theorem ofMatrix_symm_fromRows (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A) :
    ofMatrix.symm (fromRows M₁ M₂) = Matrix.fromRows (ofMatrix.symm M₁) (ofMatrix.symm M₂) := (rfl)
@[simp] theorem of_fromRows (M₁ : Matrix m l A) (M₂ : Matrix o l A) :
    ofMatrix (Matrix.fromRows M₁ M₂) = fromRows (ofMatrix M₁) (ofMatrix M₂) := (rfl)
@[simp] theorem fromRows_apply_inl (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A)
    (i : m) (j : l) : fromRows M₁ M₂ (Sum.inl i) j = M₁ i j := (rfl)
@[simp] theorem fromRows_apply_inr (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A)
    (i : o) (j : l) : fromRows M₁ M₂ (Sum.inr i) j = M₂ i j := (rfl)
@[simp] theorem fromRows_inj {M₁ N₁ : CStarMatrix m l A} {M₂ N₂ : CStarMatrix o l A} :
    fromRows M₁ M₂ = fromRows N₁ N₂ ↔ M₁ = N₁ ∧ M₂ = N₂ := by
  rw [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_fromRows, ofMatrix_symm_fromRows,
    Matrix.fromRows_ext_iff]; simp [ofMatrix.symm.injective.eq_iff]
@[simp] theorem fromRows_zero [Zero A] :
    fromRows (0 : CStarMatrix m l A) (0 : CStarMatrix o l A) = 0 := by ext (_ | _) _ <;> rfl
@[simp] theorem fromRows_add [Add A] (M₁ N₁ : CStarMatrix m l A) (M₂ N₂ : CStarMatrix o l A) :
    fromRows M₁ M₂ + fromRows N₁ N₂ = fromRows (M₁ + N₁) (M₂ + N₂) := by ext (_ | _) _ <;> rfl
@[simp] theorem fromRows_neg [Neg A] (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A) :
    -fromRows M₁ M₂ = fromRows (-M₁) (-M₂) := ofMatrix.symm.injective (Matrix.fromRows_neg _ _)
@[simp] theorem fromRows_sub [Sub A] (M₁ N₁ : CStarMatrix m l A) (M₂ N₂ : CStarMatrix o l A) :
    fromRows M₁ M₂ - fromRows N₁ N₂ = fromRows (M₁ - N₁) (M₂ - N₂) := by ext (_ | _) _ <;> rfl
@[simp] theorem fromRows_smul [SMul R A] (r : R) (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A) :
    r • fromRows M₁ M₂ = fromRows (r • M₁) (r • M₂) := by ext (_ | _) _ <;> rfl
@[simp] theorem map_fromRows (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A) (f : A → B) :
    (fromRows M₁ M₂).map f = fromRows (M₁.map f) (M₂.map f) :=
  ofMatrix.symm.injective (Matrix.fromRows_map _ _ f)

/-- Right-multiplication of a row-partitioned `CStarMatrix` acts on each row block. -/
@[simp] theorem fromRows_mul [Fintype l] [AddCommMonoid A] [Mul A]
    (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A) (N : CStarMatrix l n A) :
    fromRows M₁ M₂ * N = fromRows (M₁ * N) (M₂ * N) := by ext (_ | _) _ <;> simp [mul_apply]

/-- Inner product of two vertical row stacks as a sum of `l × n` products. -/
@[simp] theorem conjTranspose_fromRows_mul [Fintype m] [Fintype o] [NonUnitalNonAssocSemiring A]
    [Star A] (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A)
    (N₁ : CStarMatrix m n A) (N₂ : CStarMatrix o n A) :
    (fromRows M₁ M₂).conjTranspose * fromRows N₁ N₂ =
      M₁.conjTranspose * N₁ + M₂.conjTranspose * N₂ := by
  ext; simp [mul_apply, Fintype.sum_sum_type]

/-- Outer product of two vertical row stacks as a four-block `CStarMatrix`. -/
theorem fromRows_mul_conjTranspose [Fintype l] [NonUnitalNonAssocSemiring A] [Star A]
    (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A)
    (N₁ : CStarMatrix k l A) (N₂ : CStarMatrix p l A) :
    fromRows M₁ M₂ * (fromRows N₁ N₂).conjTranspose = fromBlocks (M₁ * N₁.conjTranspose)
      (M₁ * N₂.conjTranspose) (M₂ * N₁.conjTranspose) (M₂ * N₂.conjTranspose) := by
  ext (_ | _) (_ | _) <;> simp [mul_apply]

/-- Action of a four-block `CStarMatrix` on a vertical row stack. -/
@[simp] theorem fromBlocks_mul_fromRows [Fintype l] [Fintype n] [NonUnitalNonAssocSemiring A]
    (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A) (M₂₁ : CStarMatrix o l A)
    (M₂₂ : CStarMatrix o n A) (N₁ : CStarMatrix l k A) (N₂ : CStarMatrix n k A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromRows N₁ N₂ =
      fromRows (M₁₁ * N₁ + M₁₂ * N₂) (M₂₁ * N₁ + M₂₂ * N₂) := by
  ext (_ | _) _ <;> simp [mul_apply, Fintype.sum_sum_type]

/-- The block-diagonal direct sum `M ⊕ N` of two rectangular `CStarMatrix` values. -/
def blockSum [Zero A] (M : CStarMatrix m l A) (N : CStarMatrix o n A) :
    CStarMatrix (m ⊕ o) (l ⊕ n) A := fromBlocks M 0 0 N

theorem blockSum_def [Zero A] (M : CStarMatrix m l A) (N : CStarMatrix o n A) :
    blockSum M N = fromBlocks M 0 0 N := (rfl)
@[simp] theorem blockSum_apply_inl_inl [Zero A] (M : CStarMatrix m l A) (N : CStarMatrix o n A)
    (i : m) (j : l) : blockSum M N (Sum.inl i) (Sum.inl j) = M i j := (rfl)
@[simp] theorem blockSum_apply_inl_inr [Zero A] (M : CStarMatrix m l A) (N : CStarMatrix o n A)
    (i : m) (j : n) : blockSum M N (Sum.inl i) (Sum.inr j) = 0 := (rfl)
@[simp] theorem blockSum_apply_inr_inl [Zero A] (M : CStarMatrix m l A) (N : CStarMatrix o n A)
    (i : o) (j : l) : blockSum M N (Sum.inr i) (Sum.inl j) = 0 := (rfl)
@[simp] theorem blockSum_apply_inr_inr [Zero A] (M : CStarMatrix m l A) (N : CStarMatrix o n A)
    (i : o) (j : n) : blockSum M N (Sum.inr i) (Sum.inr j) = N i j := (rfl)
@[simp] theorem blockSum_inj [Zero A] {M₁ M₂ : CStarMatrix m l A} {N₁ N₂ : CStarMatrix o n A} :
    blockSum M₁ N₁ = blockSum M₂ N₂ ↔ M₁ = M₂ ∧ N₁ = N₂ := by simp [blockSum_def]
@[simp] theorem blockSum_zero [Zero A] :
    blockSum (0 : CStarMatrix m l A) (0 : CStarMatrix o n A) = 0 := fromBlocks_zero
@[simp] theorem blockSum_eq_zero_iff [Zero A] {M : CStarMatrix m l A} {N : CStarMatrix o n A} :
    blockSum M N = 0 ↔ M = 0 ∧ N = 0 := by rw [← blockSum_zero, blockSum_inj]
@[simp] theorem blockSum_one [DecidableEq l] [DecidableEq m] [Zero A] [One A] :
    blockSum (1 : CStarMatrix l l A) (1 : CStarMatrix m m A) = 1 := fromBlocks_one
@[simp] theorem blockSum_add [AddZeroClass A]
    (M₁ M₂ : CStarMatrix m l A) (N₁ N₂ : CStarMatrix o n A) :
    blockSum M₁ N₁ + blockSum M₂ N₂ = blockSum (M₁ + M₂) (N₁ + N₂) := by simp [blockSum_def]
@[simp] theorem blockSum_neg [SubtractionMonoid A]
    (M : CStarMatrix m l A) (N : CStarMatrix o n A) :
    -blockSum M N = blockSum (-M) (-N) := by ext (_ | _) (_ | _) <;> simp
@[simp] theorem blockSum_sub [AddGroup A]
    (M₁ M₂ : CStarMatrix m l A) (N₁ N₂ : CStarMatrix o n A) :
    blockSum M₁ N₁ - blockSum M₂ N₂ = blockSum (M₁ - M₂) (N₁ - N₂) := by simp [blockSum_def]
@[simp] theorem blockSum_smul [Zero A] [SMulZeroClass R A] (r : R)
    (M : CStarMatrix m l A) (N : CStarMatrix o n A) :
    r • blockSum M N = blockSum (r • M) (r • N) := by ext (_ | _) (_ | _) <;> simp
@[simp] theorem blockSum_mul [Fintype l] [Fintype n] [NonUnitalNonAssocSemiring A]
    (M₁ : CStarMatrix m l A) (N₁ : CStarMatrix o n A)
    (M₂ : CStarMatrix l k A) (N₂ : CStarMatrix n p A) :
    blockSum M₁ N₁ * blockSum M₂ N₂ = blockSum (M₁ * M₂) (N₁ * N₂) := by
  simp [blockSum_def, fromBlocks_mul]

/-- Action of a block-diagonal `CStarMatrix` on a vertical row stack. -/
@[simp] theorem blockSum_mul_fromRows [Fintype l] [Fintype n] [NonUnitalNonAssocSemiring A]
    (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o n A)
    (N₁ : CStarMatrix l k A) (N₂ : CStarMatrix n k A) :
    blockSum M₁ M₂ * fromRows N₁ N₂ = fromRows (M₁ * N₁) (M₂ * N₂) := by simp [blockSum_def]

@[simp] theorem blockSum_conjTranspose [AddMonoid A] [StarAddMonoid A]
    (M : CStarMatrix m l A) (N : CStarMatrix o n A) :
    (blockSum M N).conjTranspose = blockSum M.conjTranspose N.conjTranspose := by
  simp [blockSum_def]
@[simp] theorem star_blockSum [AddMonoid A] [StarAddMonoid A]
    (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    star (blockSum M N) = blockSum (star M) (star N) := blockSum_conjTranspose M N
@[simp] theorem map_blockSum [Zero A] [Zero B] (M : CStarMatrix m l A) (N : CStarMatrix o n A)
    {f : A → B} (hf : f 0 = 0) :
    (blockSum M N).map f = blockSum (M.map f) (N.map f) := by simp [blockSum_def, map_zero hf]

/-- A block-diagonal square matrix is idempotent iff both blocks are idempotent. -/
@[simp] theorem isIdempotentElem_blockSum_iff [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A]
    {P : CStarMatrix m m A} {Q : CStarMatrix n n A} :
    IsIdempotentElem (blockSum P Q) ↔ IsIdempotentElem P ∧ IsIdempotentElem Q := by
  simp [IsIdempotentElem]

/-- A block-diagonal square matrix is self-adjoint iff both blocks are self-adjoint. -/
@[simp] theorem isSelfAdjoint_blockSum_iff [AddMonoid A] [StarAddMonoid A]
    {P : CStarMatrix m m A} {Q : CStarMatrix n n A} :
    IsSelfAdjoint (blockSum P Q) ↔ IsSelfAdjoint P ∧ IsSelfAdjoint Q := by simp [IsSelfAdjoint]

/-- A block-diagonal square matrix is a star projection iff both blocks are star projections. -/
@[simp] theorem isStarProjection_blockSum_iff [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A]
    [StarAddMonoid A] {P : CStarMatrix m m A} {Q : CStarMatrix n n A} :
    IsStarProjection (blockSum P Q) ↔ IsStarProjection P ∧ IsStarProjection Q := by
  simp [isStarProjection_iff, and_and_and_comm]

@[simp] theorem reindexₗ_sumAssoc_blockSum [Semiring R] [AddCommMonoid A] [Module R A]
    (M₁ : CStarMatrix m₁ n₁ A) (M₂ : CStarMatrix m₂ n₂ A) (M₃ : CStarMatrix m₃ n₃ A) :
    reindexₗ R A (Equiv.sumAssoc m₁ m₂ m₃) (Equiv.sumAssoc n₁ n₂ n₃)
      (blockSum (blockSum M₁ M₂) M₃) = blockSum M₁ (blockSum M₂ M₃) := by
  ext (_ | _ | _) (_ | _ | _) <;> rfl
@[simp] theorem reindexₐ_sumAssoc_blockSum [Fintype l] [Fintype m] [Fintype n] [Semiring R]
    [AddCommMonoid A] [Mul A] [Module R A] [Star A]
    (M₁ : CStarMatrix l l A) (M₂ : CStarMatrix m m A) (M₃ : CStarMatrix n n A) :
    reindexₐ R A (Equiv.sumAssoc l m n) (blockSum (blockSum M₁ M₂) M₃) =
      blockSum M₁ (blockSum M₂ M₃) := by ext (_ | _ | _) (_ | _ | _) <;> rfl
@[simp] theorem reindexₗ_sumComm_blockSum [Semiring R] [AddCommMonoid A] [Module R A]
    (M₁ : CStarMatrix m₁ n₁ A) (M₂ : CStarMatrix m₂ n₂ A) :
    reindexₗ R A (Equiv.sumComm m₁ m₂) (Equiv.sumComm n₁ n₂) (blockSum M₁ M₂) =
      blockSum M₂ M₁ := by ext (_ | _) (_ | _) <;> rfl
@[simp] theorem reindexₐ_sumComm_blockSum [Fintype m] [Fintype n] [Semiring R] [AddCommMonoid A]
    [Mul A] [Module R A] [Star A] (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    reindexₐ R A (Equiv.sumComm m n) (blockSum M N) = blockSum N M := by
  ext (_ | _) (_ | _) <;> rfl

/-- `blockSum` bundled as a non-unital `⋆`-algebra homomorphism from the product of two square
matrix algebras into the `(m ⊕ n) × (m ⊕ n)` matrix algebra. -/
def blockSumNonUnitalStarAlgHom (R : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A where
  toFun P := blockSum P.1 P.2
  map_smul' r P := (blockSum_smul r P.1 P.2).symm
  map_zero' := blockSum_zero
  map_add' P Q := (blockSum_add P.1 Q.1 P.2 Q.2).symm
  map_mul' P Q := (blockSum_mul P.1 P.2 Q.1 Q.2).symm
  map_star' P := (star_blockSum P.1 P.2).symm

@[simp] theorem blockSumNonUnitalStarAlgHom_apply [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (P : CStarMatrix m m A × CStarMatrix n n A) :
    blockSumNonUnitalStarAlgHom R P = blockSum P.1 P.2 := (rfl)

/-- The block-diagonal direct sum homomorphism `blockSumNonUnitalStarAlgHom` is injective. -/
theorem blockSumNonUnitalStarAlgHom_injective [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    Function.Injective (blockSumNonUnitalStarAlgHom R :
      CStarMatrix m m A × CStarMatrix n n A → CStarMatrix (m ⊕ n) (m ⊕ n) A) :=
  fun _ _ h => Prod.ext (blockSum_inj.mp h).1 (blockSum_inj.mp h).2

/-- Upper-left corner inclusion `M ↦ blockSum M 0` as a non-unital `⋆`-algebra homomorphism. -/
def inlNonUnitalStarAlgHom (R n : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix m m A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (blockSumNonUnitalStarAlgHom R).comp (.inl R _ _)

@[simp] theorem inlNonUnitalStarAlgHom_apply [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (M : CStarMatrix m m A) :
    inlNonUnitalStarAlgHom R n M = blockSum M 0 := (rfl)

/-- Lower-right corner inclusion `N ↦ blockSum 0 N` as a non-unital `⋆`-algebra homomorphism. -/
def inrNonUnitalStarAlgHom (R m : Type*) [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (blockSumNonUnitalStarAlgHom R).comp (.inr R _ _)

@[simp] theorem inrNonUnitalStarAlgHom_apply [Fintype m] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] (N : CStarMatrix n n A) :
    inrNonUnitalStarAlgHom R m N = blockSum 0 N := (rfl)

end Blocks

section Amplify

variable {k l m n R A B : Type*}

/-- Finite block-diagonal amplification `1_k ⊗ M` of a rectangular `M : CStarMatrix m n A`,
placing a copy of `M` in each `(i, i)` block for `i : k` and `0` off the `k`-diagonal. -/
def amplify (k : Type*) [DecidableEq k] [Zero A] (M : CStarMatrix m n A) :
    CStarMatrix (k × m) (k × n) A :=
  ofMatrix (Matrix.reindex (.prodComm m k) (.prodComm n k)
    (Matrix.blockDiagonal fun _ : k => ofMatrix.symm M))

@[simp] theorem ofMatrix_symm_amplify [DecidableEq k] [Zero A] (M : CStarMatrix m n A) :
    ofMatrix.symm (amplify k M) = Matrix.reindex (.prodComm m k) (.prodComm n k)
      (Matrix.blockDiagonal fun _ : k => ofMatrix.symm M) := (rfl)
@[simp] theorem amplify_apply [DecidableEq k] [Zero A] (M : CStarMatrix m n A)
    (i : k × m) (j : k × n) : amplify k M i j = if i.1 = j.1 then M i.2 j.2 else 0 := (rfl)
@[simp] theorem amplify_zero [DecidableEq k] [Zero A] :
    amplify k (0 : CStarMatrix m n A) = 0 := by ext; simp
@[simp] theorem amplify_one [DecidableEq k] [DecidableEq n] [Zero A] [One A] :
    amplify k (1 : CStarMatrix n n A) = 1 := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [one_apply, Prod.ext_iff, ite_and]
@[simp] theorem amplify_add [DecidableEq k] [AddZeroClass A] (M N : CStarMatrix m n A) :
    amplify k (M + N) = amplify k M + amplify k N := by ext i j; by_cases h : i.1 = j.1 <;> simp [h]
@[simp] theorem amplify_neg [DecidableEq k] [SubtractionMonoid A] (M : CStarMatrix m n A) :
    amplify k (-M) = -amplify k M := by ext i j; by_cases h : i.1 = j.1 <;> simp [h]
@[simp] theorem amplify_sub [DecidableEq k] [AddGroup A] (M N : CStarMatrix m n A) :
    amplify k (M - N) = amplify k M - amplify k N := by ext i j; by_cases h : i.1 = j.1 <;> simp [h]
@[simp] theorem amplify_smul [DecidableEq k] [Zero A] [SMulZeroClass R A]
    (r : R) (M : CStarMatrix m n A) :
    amplify k (r • M) = r • amplify k M := by ext i j; by_cases h : i.1 = j.1 <;> simp [h]
@[simp] theorem amplify_mul [Fintype k] [DecidableEq k] [Fintype m] [NonUnitalNonAssocSemiring A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    amplify k (M * N) = amplify k M * amplify k N :=
  ofMatrix.symm.injective <| by
    simp only [ofMatrix_symm_amplify, ofMatrix_symm_mul, Matrix.reindex_apply,
      Matrix.blockDiagonal_mul]
    exact (Matrix.submatrix_mul_equiv _ _ _ (Equiv.prodComm m k).symm _).symm
@[simp] theorem amplify_conjTranspose [DecidableEq k] [AddMonoid A] [StarAddMonoid A]
    (M : CStarMatrix m n A) : (amplify k M).conjTranspose = amplify k M.conjTranspose := by
  ext ⟨i₁, _⟩ ⟨j₁, _⟩; by_cases h : i₁ = j₁ <;> simp [h, eq_comm]
@[simp] theorem star_amplify [DecidableEq k] [AddMonoid A] [StarAddMonoid A]
    (M : CStarMatrix n n A) : star (amplify k M) = amplify k (star M) := amplify_conjTranspose M
@[simp] theorem map_amplify [DecidableEq k] [Zero A] [Zero B] (M : CStarMatrix m n A)
    {f : A → B} (hf : f 0 = 0) : (amplify k M).map f = amplify k (M.map f) := by
  ext i j; by_cases h : i.1 = j.1 <;> simp [h, hf]

/-- Finite block-diagonal amplification over a nonempty index type `k` is injective. -/
theorem amplify_injective [DecidableEq k] [Nonempty k] [Zero A] :
    Function.Injective (amplify k : CStarMatrix m n A → CStarMatrix (k × m) (k × n) A) := by
  obtain ⟨x⟩ := ‹Nonempty k›
  exact fun _ _ h => ext fun i j => by simpa using congr_fun (congr_fun h (x, i)) (x, j)

/-- Finite block-diagonal amplification bundled as a non-unital `⋆`-algebra homomorphism. -/
def amplifyNonUnitalStarAlgHom (R k : Type*) [Fintype k] [DecidableEq k] [Fintype n] [Semiring R]
    [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (k × n) (k × n) A where
  toFun := amplify k
  map_smul' := amplify_smul
  map_zero' := amplify_zero
  map_add' := amplify_add
  map_mul' := amplify_mul
  map_star' M := (star_amplify M).symm

@[simp] theorem amplifyNonUnitalStarAlgHom_apply [Fintype k] [DecidableEq k] [Fintype n]
    [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [StarAddMonoid A]
    (M : CStarMatrix n n A) : amplifyNonUnitalStarAlgHom R k M = amplify k M := (rfl)

/-- Unital finite block-diagonal amplification bundled as a `⋆`-algebra homomorphism. -/
def amplifyStarAlgHom (R k : Type*) [Fintype k] [DecidableEq k] [Fintype n] [DecidableEq n]
    [CommSemiring R] [Semiring A] [Algebra R A] [StarAddMonoid A] :
    CStarMatrix n n A →⋆ₐ[R] CStarMatrix (k × n) (k × n) A :=
  { amplifyNonUnitalStarAlgHom R k with
    map_one' := amplify_one
    commutes' r := by ext ⟨_, _⟩ ⟨_, _⟩; simp [algebraMap_apply, Prod.ext_iff, ite_and] }

@[simp] theorem amplifyStarAlgHom_apply [Fintype k] [DecidableEq k] [Fintype n] [DecidableEq n]
    [CommSemiring R] [Semiring A] [Algebra R A] [StarAddMonoid A]
    (M : CStarMatrix n n A) : amplifyStarAlgHom R k M = amplify k M := (rfl)

end Amplify

section Norms
variable {k l m n o A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The operator norm of a block-diagonal `CStarMatrix` is the maximum of its block norms. -/
@[simp] theorem norm_blockSum [Fintype l] [Fintype m] [Fintype n] [Fintype o]
    (M : CStarMatrix m l A) (N : CStarMatrix o n A) : ‖blockSum M N‖ = max ‖M‖ ‖N‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (le_max_of_le_left (norm_nonneg M))).mp ?_
  have hsq : ‖blockSum (M.conjTranspose * M) (N.conjTranspose * N)‖ =
      max ‖M.conjTranspose * M‖ ‖N.conjTranspose * N‖ := by
    simpa [Prod.norm_def] using
      NonUnitalStarAlgHom.norm_map (blockSumNonUnitalStarAlgHom ℂ (m := l) (n := n) (A := A))
        blockSumNonUnitalStarAlgHom_injective (M.conjTranspose * M, N.conjTranspose * N)
  rw [← norm_conjTranspose_mul_self, blockSum_conjTranspose, blockSum_mul, hsq,
    norm_conjTranspose_mul_self, norm_conjTranspose_mul_self]
  rcases le_total ‖M‖ ‖N‖ with h | h
  · rw [max_eq_right h, max_eq_right (pow_le_pow_left₀ (norm_nonneg M) h 2)]
  · rw [max_eq_left h, max_eq_left (pow_le_pow_left₀ (norm_nonneg N) h 2)]

/-- Finite block-diagonal amplification over a nonempty index type `k` is isometric. -/
@[simp] theorem norm_amplify [Fintype k] [DecidableEq k] [Nonempty k] [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) : ‖amplify k M‖ = ‖M‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  have hinj : Function.Injective
      (amplifyNonUnitalStarAlgHom ℂ k : CStarMatrix n n A → CStarMatrix (k × n) (k × n) A) :=
    amplify_injective
  rw [← norm_conjTranspose_mul_self, amplify_conjTranspose, ← amplify_mul,
    ← amplifyNonUnitalStarAlgHom_apply (R := ℂ),
    NonUnitalStarAlgHom.norm_map (amplifyNonUnitalStarAlgHom ℂ k) hinj _,
    norm_conjTranspose_mul_self]

/-- Finite block-diagonal amplification over any finite index type `k` is contractive. -/
theorem norm_amplify_le [Fintype k] [DecidableEq k] [Fintype m] [Fintype n]
    (M : CStarMatrix m n A) : ‖amplify k M‖ ≤ ‖M‖ := by
  rcases isEmpty_or_nonempty k with hk | hk
  · have h0 : amplify k M = 0 := ext fun ⟨i, _⟩ _ => isEmptyElim i
    rw [h0, norm_zero]; exact norm_nonneg M
  · exact (norm_amplify M).le
end Norms

section Continuity
variable {k l m n o A : Type*} [NonUnitalCStarAlgebra A]

/-- A four-block `CStarMatrix` family is continuous when each of its four blocks is continuous. -/
@[fun_prop] theorem continuous_fromBlocks {X : Type*} [TopologicalSpace X]
    {f₁₁ : X → CStarMatrix m l A} {f₁₂ : X → CStarMatrix m n A}
    {f₂₁ : X → CStarMatrix o l A} {f₂₂ : X → CStarMatrix o n A}
    (hf₁₁ : Continuous f₁₁) (hf₁₂ : Continuous f₁₂)
    (hf₂₁ : Continuous f₂₁) (hf₂₂ : Continuous f₂₂) :
    Continuous fun x => fromBlocks (f₁₁ x) (f₁₂ x) (f₂₁ x) (f₂₂ x) :=
  ofMatrixL.continuous.comp <| (ofMatrixL.symm.continuous.comp hf₁₁).matrix_fromBlocks
    (ofMatrixL.symm.continuous.comp hf₁₂) (ofMatrixL.symm.continuous.comp hf₂₁)
    (ofMatrixL.symm.continuous.comp hf₂₂)

/-- A block-diagonal `CStarMatrix` family is continuous when both diagonal blocks are continuous. -/
@[fun_prop] theorem continuous_blockSum {X : Type*} [TopologicalSpace X]
    {f : X → CStarMatrix m l A} {g : X → CStarMatrix o n A}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => blockSum (f x) (g x) :=
  continuous_fromBlocks hf continuous_const continuous_const hg

/-- Finite block-diagonal amplification of a continuous `CStarMatrix` family is continuous. -/
@[fun_prop] theorem continuous_amplify {X : Type*} [TopologicalSpace X] [DecidableEq k]
    {f : X → CStarMatrix m n A} (hf : Continuous f) : Continuous fun x => amplify k (f x) :=
  ofMatrixL.continuous.comp <|
    ((continuous_pi fun _ : k => ofMatrixL.symm.continuous.comp hf).matrix_blockDiagonal
      ).matrix_reindex (.prodComm m k) (.prodComm n k)
end Continuity
end CStarMatrix
