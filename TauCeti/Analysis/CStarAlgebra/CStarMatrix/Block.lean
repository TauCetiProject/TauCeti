/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Norm
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Block calculus, amplification, and operator norms for `CStarMatrix`

Rectangular block operations on `CStarMatrix m n A`: four-block matrices (`fromBlocks`,
`toBlocks₁₁`–`toBlocks₂₂`, `ext_iff_blocks`), row stacks (`fromRows`), block-diagonal direct sums
(`blockSum`, `blockSumNonUnitalStarAlgHom`, `inlNonUnitalStarAlgHom`, `inrNonUnitalStarAlgHom`),
amplification (`amplify`, `amplifyNonUnitalStarAlgHom`, `amplifyStarAlgHom`), operator-norm laws
(`norm_toBlocks₁₁_le`–`₂₂_le`, `norm_fromBlocks_le`, `norm_blockSum`, `norm_amplify`), and
`@[fun_prop]` continuity.

## Main declarations

* `CStarMatrix.fromBlocks`, `toBlocks₁₁`–`toBlocks₂₂`, `ext_iff_blocks`, `fromRows`, `blockSum`,
  `amplify`, `blockSumNonUnitalStarAlgHom`, `inlNonUnitalStarAlgHom`, `inrNonUnitalStarAlgHom`,
  `amplifyNonUnitalStarAlgHom`, `amplifyStarAlgHom`, `norm_toBlocks₁₁_le`, `norm_fromBlocks_le`,
  `norm_blockSum`, `norm_amplify`, `continuous_fromBlocks`–`continuous_amplify`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §4.6 and §5.1; E. C. Lance, *Hilbert
  C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 4.
-/

public section

open scoped Matrix ComplexOrder

namespace CStarMatrix

section Blocks
variable {k l m n o p m₁ m₂ m₃ n₁ n₂ n₃ R A B : Type*}
/-- Build a four-block `CStarMatrix` from blocks of sizes `m × l`, `m × n`, `o × l`, and `o × n`. -/
def fromBlocks (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A) (M₂₁ : CStarMatrix o l A)
    (M₂₂ : CStarMatrix o n A) : CStarMatrix (m ⊕ o) (l ⊕ n) A :=
  ofMatrix (Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
    (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂))
@[simp] theorem of_fromBlocks (M₁₁ : Matrix m l A) (M₁₂ : Matrix m n A)
    (M₂₁ : Matrix o l A) (M₂₂ : Matrix o n A) : ofMatrix (Matrix.fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (ofMatrix M₁₁) (ofMatrix M₁₂) (ofMatrix M₂₁) (ofMatrix M₂₂) := (rfl)
section
variable (M N : CStarMatrix (m ⊕ o) (l ⊕ n) A)
/-- Extract the upper-left `m × l` block of `M : CStarMatrix (m ⊕ o) (l ⊕ n) A`. -/
def toBlocks₁₁ : CStarMatrix m l A := ofMatrix (ofMatrix.symm M).toBlocks₁₁
/-- Extract the upper-right `m × n` block of `M : CStarMatrix (m ⊕ o) (l ⊕ n) A`. -/
def toBlocks₁₂ : CStarMatrix m n A := ofMatrix (ofMatrix.symm M).toBlocks₁₂
/-- Extract the lower-left `o × l` block of `M : CStarMatrix (m ⊕ o) (l ⊕ n) A`. -/
def toBlocks₂₁ : CStarMatrix o l A := ofMatrix (ofMatrix.symm M).toBlocks₂₁
/-- Extract the lower-right `o × n` block of `M : CStarMatrix (m ⊕ o) (l ⊕ n) A`. -/
def toBlocks₂₂ : CStarMatrix o n A := ofMatrix (ofMatrix.symm M).toBlocks₂₂
@[simp] theorem ofMatrix_symm_toBlocks₁₁ :
    ofMatrix.symm M.toBlocks₁₁ = (ofMatrix.symm M).toBlocks₁₁ := (rfl)
@[simp] theorem ofMatrix_symm_toBlocks₁₂ :
    ofMatrix.symm M.toBlocks₁₂ = (ofMatrix.symm M).toBlocks₁₂ := (rfl)
@[simp] theorem ofMatrix_symm_toBlocks₂₁ :
    ofMatrix.symm M.toBlocks₂₁ = (ofMatrix.symm M).toBlocks₂₁ := (rfl)
@[simp] theorem ofMatrix_symm_toBlocks₂₂ :
    ofMatrix.symm M.toBlocks₂₂ = (ofMatrix.symm M).toBlocks₂₂ := (rfl)
@[simp] theorem toBlocks₁₁_apply (i : m) (j : l) : M.toBlocks₁₁ i j = M (.inl i) (.inl j) := (rfl)
@[simp] theorem toBlocks₁₂_apply (i : m) (j : n) : M.toBlocks₁₂ i j = M (.inl i) (.inr j) := (rfl)
@[simp] theorem toBlocks₂₁_apply (i : o) (j : l) : M.toBlocks₂₁ i j = M (.inr i) (.inl j) := (rfl)
@[simp] theorem toBlocks₂₂_apply (i : o) (j : n) : M.toBlocks₂₂ i j = M (.inr i) (.inr j) := (rfl)
/-- Reassembling the four extracted blocks of `M` recovers `M`. -/
@[simp] theorem fromBlocks_toBlocks :
    fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ = M :=
  ofMatrix.symm.injective (Matrix.fromBlocks_toBlocks (ofMatrix.symm M))
@[simp] theorem toBlocks₁₁_add [Add A] : (M + N).toBlocks₁₁ = M.toBlocks₁₁ + N.toBlocks₁₁ := (rfl)
@[simp] theorem toBlocks₁₂_add [Add A] : (M + N).toBlocks₁₂ = M.toBlocks₁₂ + N.toBlocks₁₂ := (rfl)
@[simp] theorem toBlocks₂₁_add [Add A] : (M + N).toBlocks₂₁ = M.toBlocks₂₁ + N.toBlocks₂₁ := (rfl)
@[simp] theorem toBlocks₂₂_add [Add A] : (M + N).toBlocks₂₂ = M.toBlocks₂₂ + N.toBlocks₂₂ := (rfl)
@[simp] theorem toBlocks₁₁_neg [Neg A] : (-M).toBlocks₁₁ = -M.toBlocks₁₁ := (rfl)
@[simp] theorem toBlocks₁₂_neg [Neg A] : (-M).toBlocks₁₂ = -M.toBlocks₁₂ := (rfl)
@[simp] theorem toBlocks₂₁_neg [Neg A] : (-M).toBlocks₂₁ = -M.toBlocks₂₁ := (rfl)
@[simp] theorem toBlocks₂₂_neg [Neg A] : (-M).toBlocks₂₂ = -M.toBlocks₂₂ := (rfl)
@[simp] theorem toBlocks₁₁_sub [Sub A] : (M - N).toBlocks₁₁ = M.toBlocks₁₁ - N.toBlocks₁₁ := (rfl)
@[simp] theorem toBlocks₁₂_sub [Sub A] : (M - N).toBlocks₁₂ = M.toBlocks₁₂ - N.toBlocks₁₂ := (rfl)
@[simp] theorem toBlocks₂₁_sub [Sub A] : (M - N).toBlocks₂₁ = M.toBlocks₂₁ - N.toBlocks₂₁ := (rfl)
@[simp] theorem toBlocks₂₂_sub [Sub A] : (M - N).toBlocks₂₂ = M.toBlocks₂₂ - N.toBlocks₂₂ := (rfl)
@[simp] theorem toBlocks₁₁_smul [SMul R A] (r : R) : (r • M).toBlocks₁₁ = r • M.toBlocks₁₁ := (rfl)
@[simp] theorem toBlocks₁₂_smul [SMul R A] (r : R) : (r • M).toBlocks₁₂ = r • M.toBlocks₁₂ := (rfl)
@[simp] theorem toBlocks₂₁_smul [SMul R A] (r : R) : (r • M).toBlocks₂₁ = r • M.toBlocks₂₁ := (rfl)
@[simp] theorem toBlocks₂₂_smul [SMul R A] (r : R) : (r • M).toBlocks₂₂ = r • M.toBlocks₂₂ := (rfl)
@[simp] theorem toBlocks₁₁_conjTranspose [Star A] :
    M.conjTranspose.toBlocks₁₁ = M.toBlocks₁₁.conjTranspose := (rfl)
@[simp] theorem toBlocks₁₂_conjTranspose [Star A] :
    M.conjTranspose.toBlocks₁₂ = M.toBlocks₂₁.conjTranspose := (rfl)
@[simp] theorem toBlocks₂₁_conjTranspose [Star A] :
    M.conjTranspose.toBlocks₂₁ = M.toBlocks₁₂.conjTranspose := (rfl)
@[simp] theorem toBlocks₂₂_conjTranspose [Star A] :
    M.conjTranspose.toBlocks₂₂ = M.toBlocks₂₂.conjTranspose := (rfl)
@[simp] theorem toBlocks₁₁_map (f : A → B) : (M.map f).toBlocks₁₁ = M.toBlocks₁₁.map f := (rfl)
@[simp] theorem toBlocks₁₂_map (f : A → B) : (M.map f).toBlocks₁₂ = M.toBlocks₁₂.map f := (rfl)
@[simp] theorem toBlocks₂₁_map (f : A → B) : (M.map f).toBlocks₂₁ = M.toBlocks₂₁.map f := (rfl)
@[simp] theorem toBlocks₂₂_map (f : A → B) : (M.map f).toBlocks₂₂ = M.toBlocks₂₂.map f := (rfl)
end
/-- Two four-block `CStarMatrix` values are equal iff all four extracted blocks are equal. -/
theorem ext_iff_blocks {M N : CStarMatrix (m ⊕ o) (l ⊕ n) A} :
    M = N ↔ M.toBlocks₁₁ = N.toBlocks₁₁ ∧ M.toBlocks₁₂ = N.toBlocks₁₂ ∧
      M.toBlocks₂₁ = N.toBlocks₂₁ ∧ M.toBlocks₂₂ = N.toBlocks₂₂ :=
  ⟨fun h => h ▸ ⟨rfl, rfl, rfl, rfl⟩, fun ⟨h₁₁, h₁₂, h₂₁, h₂₂⟩ => by
    rw [← fromBlocks_toBlocks M, ← fromBlocks_toBlocks N, h₁₁, h₁₂, h₂₁, h₂₂]⟩
section
variable [Zero A]
@[simp] theorem toBlocks₁₁_zero : (0 : CStarMatrix (m ⊕ o) (l ⊕ n) A).toBlocks₁₁ = 0 := (rfl)
@[simp] theorem toBlocks₁₂_zero : (0 : CStarMatrix (m ⊕ o) (l ⊕ n) A).toBlocks₁₂ = 0 := (rfl)
@[simp] theorem toBlocks₂₁_zero : (0 : CStarMatrix (m ⊕ o) (l ⊕ n) A).toBlocks₂₁ = 0 := (rfl)
@[simp] theorem toBlocks₂₂_zero : (0 : CStarMatrix (m ⊕ o) (l ⊕ n) A).toBlocks₂₂ = 0 := (rfl)
variable [DecidableEq l] [DecidableEq m] [One A]
@[simp] theorem toBlocks₁₁_one :
    (1 : CStarMatrix (l ⊕ m) (l ⊕ m) A).toBlocks₁₁ = 1 := by ext i j; simp [one_apply]
@[simp] theorem toBlocks₁₂_one : (1 : CStarMatrix (l ⊕ m) (l ⊕ m) A).toBlocks₁₂ = 0 := by ext; simp
@[simp] theorem toBlocks₂₁_one : (1 : CStarMatrix (l ⊕ m) (l ⊕ m) A).toBlocks₂₁ = 0 := by ext; simp
@[simp] theorem toBlocks₂₂_one :
    (1 : CStarMatrix (l ⊕ m) (l ⊕ m) A).toBlocks₂₂ = 1 := by ext i j; simp [one_apply]
end
section
variable [Star A] (M : CStarMatrix (m ⊕ n) (m ⊕ n) A)
@[simp] theorem toBlocks₁₁_star : (star M).toBlocks₁₁ = star M.toBlocks₁₁ := (rfl)
@[simp] theorem toBlocks₁₂_star : (star M).toBlocks₁₂ = M.toBlocks₂₁.conjTranspose := (rfl)
@[simp] theorem toBlocks₂₁_star : (star M).toBlocks₂₁ = M.toBlocks₁₂.conjTranspose := (rfl)
@[simp] theorem toBlocks₂₂_star : (star M).toBlocks₂₂ = star M.toBlocks₂₂ := (rfl)
end
section
variable (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
  (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A)
@[simp] theorem ofMatrix_symm_fromBlocks : ofMatrix.symm (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
    Matrix.fromBlocks (ofMatrix.symm M₁₁) (ofMatrix.symm M₁₂)
      (ofMatrix.symm M₂₁) (ofMatrix.symm M₂₂) := (rfl)
@[simp] theorem toBlocks_fromBlocks₁₁ : (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).toBlocks₁₁ = M₁₁ := (rfl)
@[simp] theorem toBlocks_fromBlocks₁₂ : (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).toBlocks₁₂ = M₁₂ := (rfl)
@[simp] theorem toBlocks_fromBlocks₂₁ : (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).toBlocks₂₁ = M₂₁ := (rfl)
@[simp] theorem toBlocks_fromBlocks₂₂ : (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).toBlocks₂₂ = M₂₂ := (rfl)
@[simp] theorem fromBlocks_apply₁₁ (i : m) (j : l) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (.inl i) (.inl j) = M₁₁ i j := (rfl)
@[simp] theorem fromBlocks_apply₁₂ (i : m) (j : n) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (.inl i) (.inr j) = M₁₂ i j := (rfl)
@[simp] theorem fromBlocks_apply₂₁ (i : o) (j : l) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (.inr i) (.inl j) = M₂₁ i j := (rfl)
@[simp] theorem fromBlocks_apply₂₂ (i : o) (j : n) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ (.inr i) (.inr j) = M₂₂ i j := (rfl)
@[simp] theorem fromBlocks_neg [Neg A] : -fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ =
    fromBlocks (-M₁₁) (-M₁₂) (-M₂₁) (-M₂₂) := by ext (_ | _) (_ | _) <;> rfl
@[simp] theorem fromBlocks_smul [SMul R A] (r : R) : r • fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ =
    fromBlocks (r • M₁₁) (r • M₁₂) (r • M₂₁) (r • M₂₂) := by ext (_ | _) (_ | _) <;> rfl
/-- Conjugate transpose of a four-block `CStarMatrix`. -/
@[simp] theorem fromBlocks_conjTranspose [Star A] : (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).conjTranspose =
    fromBlocks M₁₁.conjTranspose M₂₁.conjTranspose M₁₂.conjTranspose M₂₂.conjTranspose :=
  ofMatrix.symm.injective (Matrix.fromBlocks_conjTranspose _ _ _ _)
@[simp] theorem map_fromBlocks (f : A → B) : (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂).map f =
    fromBlocks (M₁₁.map f) (M₁₂.map f) (M₂₁.map f) (M₂₂.map f) := by ext (_ | _) (_ | _) <;> rfl
/-- Block-by-block multiplication of `CStarMatrix.fromBlocks`. -/
theorem fromBlocks_mul [Fintype l] [Fintype n] [AddCommMonoid A] [Mul A]
    (N₁₁ : CStarMatrix l k A) (N₁₂ : CStarMatrix l p A)
    (N₂₁ : CStarMatrix n k A) (N₂₂ : CStarMatrix n p A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
      fromBlocks (M₁₁ * N₁₁ + M₁₂ * N₂₁) (M₁₁ * N₁₂ + M₁₂ * N₂₂)
        (M₂₁ * N₁₁ + M₂₂ * N₂₁) (M₂₁ * N₁₂ + M₂₂ * N₂₂) := by
  ext (_ | _) (_ | _) <;> simp [mul_apply, Fintype.sum_sum_type]
end
@[simp] theorem fromBlocks_inj {M₁₁ N₁₁ : CStarMatrix m l A} {M₁₂ N₁₂ : CStarMatrix m n A}
    {M₂₁ N₂₁ : CStarMatrix o l A} {M₂₂ N₂₂ : CStarMatrix o n A} :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ ↔
      M₁₁ = N₁₁ ∧ M₁₂ = N₁₂ ∧ M₂₁ = N₂₁ ∧ M₂₂ = N₂₂ := by simp [ext_iff_blocks]
@[simp] theorem fromBlocks_zero [Zero A] :
    fromBlocks (0 : CStarMatrix m l A) 0 0 (0 : CStarMatrix o n A) = 0 := by simp [ext_iff_blocks]
@[simp] theorem fromBlocks_eq_zero_iff [Zero A] {M₁₁ : CStarMatrix m l A} {M₁₂ : CStarMatrix m n A}
    {M₂₁ : CStarMatrix o l A} {M₂₂ : CStarMatrix o n A} :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = 0 ↔ M₁₁ = 0 ∧ M₁₂ = 0 ∧ M₂₁ = 0 ∧ M₂₂ = 0 := by
  rw [← fromBlocks_zero, fromBlocks_inj]
@[simp] theorem fromBlocks_one [DecidableEq l] [DecidableEq m] [Zero A] [One A] :
    fromBlocks (1 : CStarMatrix l l A) 0 0 (1 : CStarMatrix m m A) = 1 := by simp [ext_iff_blocks]
section
variable (M₁₁ N₁₁ : CStarMatrix m l A) (M₁₂ N₁₂ : CStarMatrix m n A)
  (M₂₁ N₂₁ : CStarMatrix o l A) (M₂₂ N₂₂ : CStarMatrix o n A)
@[simp] theorem fromBlocks_add [Add A] : fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ + fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
    fromBlocks (M₁₁ + N₁₁) (M₁₂ + N₁₂) (M₂₁ + N₂₁) (M₂₂ + N₂₂) := by ext (_ | _) (_ | _) <;> rfl
@[simp] theorem fromBlocks_sub [Sub A] : fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ - fromBlocks N₁₁ N₁₂ N₂₁ N₂₂ =
    fromBlocks (M₁₁ - N₁₁) (M₁₂ - N₁₂) (M₂₁ - N₂₁) (M₂₂ - N₂₂) := by ext (_ | _) (_ | _) <;> rfl
end
/-- `star` of a square four-block `CStarMatrix`. -/
@[simp] theorem star_fromBlocks [Star A] (M₁₁ : CStarMatrix m m A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix n m A) (M₂₂ : CStarMatrix n n A) : star (fromBlocks M₁₁ M₁₂ M₂₁ M₂₂) =
      fromBlocks (star M₁₁) M₂₁.conjTranspose M₁₂.conjTranspose (star M₂₂) :=
  fromBlocks_conjTranspose M₁₁ M₁₂ M₂₁ M₂₂
section
variable (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A)
/-- Stack matrices of sizes `m × l` and `o × l` vertically into a `(m ⊕ o) × l` `CStarMatrix`. -/
def fromRows : CStarMatrix (m ⊕ o) l A :=
  ofMatrix (Matrix.fromRows (ofMatrix.symm M₁) (ofMatrix.symm M₂))
@[simp] theorem ofMatrix_symm_fromRows :
    ofMatrix.symm (fromRows M₁ M₂) = Matrix.fromRows (ofMatrix.symm M₁) (ofMatrix.symm M₂) := (rfl)
@[simp] theorem fromRows_apply_inl (i : m) (j : l) : fromRows M₁ M₂ (.inl i) j = M₁ i j := (rfl)
@[simp] theorem fromRows_apply_inr (i : o) (j : l) : fromRows M₁ M₂ (.inr i) j = M₂ i j := (rfl)
@[simp] theorem fromRows_neg [Neg A] : -fromRows M₁ M₂ = fromRows (-M₁) (-M₂) :=
  ofMatrix.symm.injective (Matrix.fromRows_neg _ _)
@[simp] theorem map_fromRows (f : A → B) : (fromRows M₁ M₂).map f =
    fromRows (M₁.map f) (M₂.map f) := ofMatrix.symm.injective (Matrix.fromRows_map _ _ f)
/-- Right-multiplication of a row-partitioned `CStarMatrix` acts on each row block. -/
@[simp] theorem fromRows_mul [Fintype l] [AddCommMonoid A] [Mul A] (N : CStarMatrix l n A) :
    fromRows M₁ M₂ * N = fromRows (M₁ * N) (M₂ * N) := by ext (_ | _) _ <;> simp [mul_apply]
/-- Inner product of two vertical row stacks as a sum of `l × n` products. -/
@[simp] theorem conjTranspose_fromRows_mul_fromRows [Fintype m] [Fintype o]
    [AddCommMonoid A] [Mul A] [Star A] (N₁ : CStarMatrix m n A) (N₂ : CStarMatrix o n A) :
    (fromRows M₁ M₂).conjTranspose * fromRows N₁ N₂ =
      M₁.conjTranspose * N₁ + M₂.conjTranspose * N₂ := by
  ext; simp [mul_apply, Fintype.sum_sum_type]
/-- Outer product of two vertical row stacks as a four-block `CStarMatrix`. -/
theorem fromRows_mul_conjTranspose_fromRows [Fintype l] [AddCommMonoid A] [Mul A] [Star A]
    (N₁ : CStarMatrix k l A) (N₂ : CStarMatrix p l A) :
    fromRows M₁ M₂ * (fromRows N₁ N₂).conjTranspose = fromBlocks (M₁ * N₁.conjTranspose)
      (M₁ * N₂.conjTranspose) (M₂ * N₁.conjTranspose) (M₂ * N₂.conjTranspose) := by
  ext (_ | _) (_ | _) <;> simp [mul_apply]
end
@[simp] theorem of_fromRows (M₁ : Matrix m l A) (M₂ : Matrix o l A) :
    ofMatrix (Matrix.fromRows M₁ M₂) = fromRows (ofMatrix M₁) (ofMatrix M₂) := (rfl)
@[simp] theorem fromRows_inj {M₁ N₁ : CStarMatrix m l A} {M₂ N₂ : CStarMatrix o l A} :
    fromRows M₁ M₂ = fromRows N₁ N₂ ↔ M₁ = N₁ ∧ M₂ = N₂ := by
  simp only [← ofMatrix.symm.injective.eq_iff, ofMatrix_symm_fromRows, Matrix.fromRows_ext_iff]
@[simp] theorem fromRows_zero [Zero A] :
    fromRows (0 : CStarMatrix m l A) (0 : CStarMatrix o l A) = 0 := by ext (_ | _) _ <;> rfl
@[simp] theorem fromRows_eq_zero_iff [Zero A] {M₁ : CStarMatrix m l A} {M₂ : CStarMatrix o l A} :
    fromRows M₁ M₂ = 0 ↔ M₁ = 0 ∧ M₂ = 0 := by rw [← fromRows_zero, fromRows_inj]
@[simp] theorem fromRows_add [Add A] (M₁ N₁ : CStarMatrix m l A) (M₂ N₂ : CStarMatrix o l A) :
    fromRows M₁ M₂ + fromRows N₁ N₂ = fromRows (M₁ + N₁) (M₂ + N₂) := by ext (_ | _) _ <;> rfl
@[simp] theorem fromRows_sub [Sub A] (M₁ N₁ : CStarMatrix m l A) (M₂ N₂ : CStarMatrix o l A) :
    fromRows M₁ M₂ - fromRows N₁ N₂ = fromRows (M₁ - N₁) (M₂ - N₂) := by ext (_ | _) _ <;> rfl
@[simp] theorem fromRows_smul [SMul R A] (r : R) (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o l A) :
    r • fromRows M₁ M₂ = fromRows (r • M₁) (r • M₂) := by ext (_ | _) _ <;> rfl
/-- Action of a four-block `CStarMatrix` on a vertical row stack. -/
@[simp] theorem fromBlocks_mul_fromRows [Fintype l] [Fintype n] [AddCommMonoid A] [Mul A]
    (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A) (M₂₁ : CStarMatrix o l A)
    (M₂₂ : CStarMatrix o n A) (N₁ : CStarMatrix l k A) (N₂ : CStarMatrix n k A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ * fromRows N₁ N₂ =
      fromRows (M₁₁ * N₁ + M₁₂ * N₂) (M₂₁ * N₁ + M₂₂ * N₂) := by
  ext (_ | _) _ <;> simp [mul_apply, Fintype.sum_sum_type]
section
variable [Zero A]
section
variable (M : CStarMatrix m l A) (N : CStarMatrix o n A)
/-- The block-diagonal direct sum `M ⊕ N` of two rectangular `CStarMatrix` values. -/
def blockSum : CStarMatrix (m ⊕ o) (l ⊕ n) A := fromBlocks M 0 0 N
theorem blockSum_def : blockSum M N = fromBlocks M 0 0 N := (rfl)
@[simp] theorem ofMatrix_symm_blockSum : ofMatrix.symm (blockSum M N) =
    Matrix.fromBlocks (ofMatrix.symm M) 0 0 (ofMatrix.symm N) := (rfl)
@[simp] theorem toBlocks₁₁_blockSum : (blockSum M N).toBlocks₁₁ = M := (rfl)
@[simp] theorem toBlocks₁₂_blockSum : (blockSum M N).toBlocks₁₂ = 0 := (rfl)
@[simp] theorem toBlocks₂₁_blockSum : (blockSum M N).toBlocks₂₁ = 0 := (rfl)
@[simp] theorem toBlocks₂₂_blockSum : (blockSum M N).toBlocks₂₂ = N := (rfl)
@[simp] theorem blockSum_apply_inl_inl (i : m) (j : l) : blockSum M N (.inl i) (.inl j) = M i j :=
  (rfl)
@[simp] theorem blockSum_apply_inl_inr (i : m) (j : n) : blockSum M N (.inl i) (.inr j) = 0 := (rfl)
@[simp] theorem blockSum_apply_inr_inl (i : o) (j : l) : blockSum M N (.inr i) (.inl j) = 0 := (rfl)
@[simp] theorem blockSum_apply_inr_inr (i : o) (j : n) : blockSum M N (.inr i) (.inr j) = N i j :=
  (rfl)
@[simp] theorem map_blockSum [Zero B] {f : A → B} (hf : f 0 = 0) :
    (blockSum M N).map f = blockSum (M.map f) (N.map f) := by simp [blockSum_def, map_zero hf]
end
@[simp] theorem blockSum_smul [SMulZeroClass R A] (r : R) (M : CStarMatrix m l A)
    (N : CStarMatrix o n A) : r • blockSum M N = blockSum (r • M) (r • N) := by
  ext (_ | _) (_ | _) <;> simp
@[simp] theorem blockSum_inj {M₁ M₂ : CStarMatrix m l A} {N₁ N₂ : CStarMatrix o n A} :
    blockSum M₁ N₁ = blockSum M₂ N₂ ↔ M₁ = M₂ ∧ N₁ = N₂ := by simp [blockSum_def]
@[simp] theorem blockSum_zero :
    blockSum (0 : CStarMatrix m l A) (0 : CStarMatrix o n A) = 0 := fromBlocks_zero
@[simp] theorem blockSum_eq_zero_iff {M : CStarMatrix m l A} {N : CStarMatrix o n A} :
    blockSum M N = 0 ↔ M = 0 ∧ N = 0 := by rw [← blockSum_zero, blockSum_inj]
@[simp] theorem blockSum_one [DecidableEq l] [DecidableEq m] [One A] :
    blockSum (1 : CStarMatrix l l A) (1 : CStarMatrix m m A) = 1 := fromBlocks_one
end
@[simp] theorem blockSum_neg [NegZeroClass A] (M : CStarMatrix m l A) (N : CStarMatrix o n A) :
    -blockSum M N = blockSum (-M) (-N) := by ext (_ | _) (_ | _) <;> simp
@[simp] theorem blockSum_conjTranspose [AddMonoid A] [StarAddMonoid A] (M : CStarMatrix m l A)
    (N : CStarMatrix o n A) : (blockSum M N).conjTranspose =
      blockSum M.conjTranspose N.conjTranspose := by simp [blockSum_def]
@[simp] theorem blockSum_add [AddZeroClass A] (M₁ M₂ : CStarMatrix m l A)
    (N₁ N₂ : CStarMatrix o n A) : blockSum M₁ N₁ + blockSum M₂ N₂ = blockSum (M₁ + M₂) (N₁ + N₂) :=
  by simp [blockSum_def]
@[simp] theorem blockSum_sub [SubNegZeroMonoid A] (M₁ M₂ : CStarMatrix m l A)
    (N₁ N₂ : CStarMatrix o n A) : blockSum M₁ N₁ - blockSum M₂ N₂ = blockSum (M₁ - M₂) (N₁ - N₂) :=
  by ext (_ | _) (_ | _) <;> simp
@[simp] theorem blockSum_mul [Fintype l] [Fintype n] [NonUnitalNonAssocSemiring A]
    (M₁ : CStarMatrix m l A) (N₁ : CStarMatrix o n A) (M₂ : CStarMatrix l k A)
    (N₂ : CStarMatrix n p A) : blockSum M₁ N₁ * blockSum M₂ N₂ = blockSum (M₁ * M₂) (N₁ * N₂) := by
  simp [blockSum_def, fromBlocks_mul]
/-- Action of a block-diagonal `CStarMatrix` on a vertical row stack. -/
@[simp] theorem blockSum_mul_fromRows [Fintype l] [Fintype n] [NonUnitalNonAssocSemiring A]
    (M₁ : CStarMatrix m l A) (M₂ : CStarMatrix o n A) (N₁ : CStarMatrix l k A)
    (N₂ : CStarMatrix n k A) : blockSum M₁ M₂ * fromRows N₁ N₂ = fromRows (M₁ * N₁) (M₂ * N₂) := by
  simp [blockSum_def]
@[simp] theorem star_blockSum [AddMonoid A] [StarAddMonoid A] (M : CStarMatrix m m A)
    (N : CStarMatrix n n A) : star (blockSum M N) = blockSum (star M) (star N) :=
  blockSum_conjTranspose M N
section
variable {P : CStarMatrix m m A} {Q : CStarMatrix n n A}
/-- A block-diagonal square matrix is idempotent iff both blocks are idempotent. -/
@[simp] theorem isIdempotentElem_blockSum_iff [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] :
    IsIdempotentElem (blockSum P Q) ↔ IsIdempotentElem P ∧ IsIdempotentElem Q := by
  simp [IsIdempotentElem]
/-- A block-diagonal square matrix is self-adjoint iff both blocks are self-adjoint. -/
@[simp] theorem isSelfAdjoint_blockSum_iff [AddMonoid A] [StarAddMonoid A] :
    IsSelfAdjoint (blockSum P Q) ↔ IsSelfAdjoint P ∧ IsSelfAdjoint Q := by simp [IsSelfAdjoint]
/-- A block-diagonal square matrix is a star projection iff both blocks are star projections. -/
@[simp] theorem isStarProjection_blockSum_iff [Fintype m] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A] :
    IsStarProjection (blockSum P Q) ↔ IsStarProjection P ∧ IsStarProjection Q := by
  simp [isStarProjection_iff, and_and_and_comm]
end
section
variable [Semiring R] [AddCommMonoid A] [Module R A]
@[simp] theorem reindexₗ_sumAssoc_blockSum (M₁ : CStarMatrix m₁ n₁ A) (M₂ : CStarMatrix m₂ n₂ A)
    (M₃ : CStarMatrix m₃ n₃ A) : reindexₗ R A (.sumAssoc m₁ m₂ m₃) (.sumAssoc n₁ n₂ n₃)
      (blockSum (blockSum M₁ M₂) M₃) = blockSum M₁ (blockSum M₂ M₃) := by
  ext (_ | _ | _) (_ | _ | _) <;> rfl
@[simp] theorem reindexₗ_sumComm_blockSum (M₁ : CStarMatrix m₁ n₁ A) (M₂ : CStarMatrix m₂ n₂ A) :
    reindexₗ R A (Equiv.sumComm m₁ m₂) (Equiv.sumComm n₁ n₂) (blockSum M₁ M₂) =
      blockSum M₂ M₁ := by ext (_ | _) (_ | _) <;> rfl
@[simp] theorem reindexₐ_sumAssoc_blockSum [Fintype l] [Fintype m] [Fintype n] [Mul A] [Star A]
    (M₁ : CStarMatrix l l A) (M₂ : CStarMatrix m m A) (M₃ : CStarMatrix n n A) :
    reindexₐ R A (Equiv.sumAssoc l m n) (blockSum (blockSum M₁ M₂) M₃) =
      blockSum M₁ (blockSum M₂ M₃) := by ext (_ | _ | _) (_ | _ | _) <;> rfl
@[simp] theorem reindexₐ_sumComm_blockSum [Fintype m] [Fintype n] [Mul A] [Star A]
    (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    reindexₐ R A (.sumComm m n) (blockSum M N) = blockSum N M := by ext (_ | _) (_ | _) <;> rfl
end
/-- Conjugating `blockSum (blockSum M₁ M₂) M₃` by `permMatrix A (Equiv.sumAssoc l m n)`
reassociates the blocks to `blockSum M₁ (blockSum M₂ M₃)`. -/
theorem permMatrix_conj_sumAssoc_blockSum [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [NonAssocSemiring A] [StarRing A]
    (M₁ : CStarMatrix l l A) (M₂ : CStarMatrix m m A) (M₃ : CStarMatrix n n A) :
    (permMatrix A (Equiv.sumAssoc l m n)).conjTranspose * blockSum (blockSum M₁ M₂) M₃ *
      permMatrix A (Equiv.sumAssoc l m n) = blockSum M₁ (blockSum M₂ M₃) := by
  rw [permMatrix_conj_eq_reindexₐ (R := ℕ), reindexₐ_sumAssoc_blockSum]
/-- Conjugating `blockSum M N` by `permMatrix A (.sumComm m n)` swaps the blocks to
`blockSum N M`. -/
theorem permMatrix_conj_sumComm_blockSum [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NonAssocSemiring A] [StarRing A]
    (M : CStarMatrix m m A) (N : CStarMatrix n n A) :
    (permMatrix A (Equiv.sumComm m n)).conjTranspose * blockSum M N *
      permMatrix A (Equiv.sumComm m n) = blockSum N M := by
  rw [permMatrix_conj_eq_reindexₐ (R := ℕ), reindexₐ_sumComm_blockSum]
/-- Decompose a four-block `CStarMatrix` into a diagonal `blockSum` plus a column-swapped
off-diagonal `blockSum`. -/
theorem fromBlocks_eq_blockSum_add_reindexₗ (R : Type*) [Semiring R] [AddCommMonoid A] [Module R A]
    (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    fromBlocks M₁₁ M₁₂ M₂₁ M₂₂ = blockSum M₁₁ M₂₂ +
      reindexₗ R A (.refl _) (.sumComm n l) (blockSum M₁₂ M₂₁) := by
  ext (_ | _) (_ | _) <;> simp [Matrix.reindex, Matrix.submatrix]
section
variable [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
/-- `blockSum` bundled as a non-unital `⋆`-algebra homomorphism on square matrix algebras. -/
def blockSumNonUnitalStarAlgHom (R : Type*) [Semiring R] [Module R A] :
    CStarMatrix m m A × CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  { toFun := fun P => blockSum P.1 P.2, map_smul' := fun r P => (blockSum_smul r P.1 P.2).symm,
    map_zero' := blockSum_zero, map_add' := fun P Q => (blockSum_add P.1 Q.1 P.2 Q.2).symm,
    map_mul' := fun P Q => (blockSum_mul P.1 P.2 Q.1 Q.2).symm,
    map_star' := fun P => (star_blockSum P.1 P.2).symm }
variable [Semiring R] [Module R A]
@[simp low] theorem blockSumNonUnitalStarAlgHom_apply (P : CStarMatrix m m A × CStarMatrix n n A) :
    blockSumNonUnitalStarAlgHom R P = blockSum P.1 P.2 := (rfl)
/-- The block-diagonal direct sum homomorphism `blockSumNonUnitalStarAlgHom` is injective. -/
theorem blockSumNonUnitalStarAlgHom_injective : Function.Injective (blockSumNonUnitalStarAlgHom R
    (m := m) (n := n) (A := A)) := fun _ _ h => Prod.ext (blockSum_inj.mp h).1 (blockSum_inj.mp h).2
/-- Upper-left corner inclusion `M ↦ blockSum M 0` as a non-unital `⋆`-algebra homomorphism. -/
def inlNonUnitalStarAlgHom (R n : Type*) [Semiring R] [Fintype n] [Module R A] :
    CStarMatrix m m A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (blockSumNonUnitalStarAlgHom R).comp (.inl R _ _)
@[simp low] theorem inlNonUnitalStarAlgHom_apply (M : CStarMatrix m m A) :
    inlNonUnitalStarAlgHom R n M = blockSum M 0 := (rfl)
/-- The upper-left corner inclusion `inlNonUnitalStarAlgHom` is injective. -/
theorem inlNonUnitalStarAlgHom_injective : Function.Injective
    (inlNonUnitalStarAlgHom R n (m := m) (A := A)) := fun _ _ h => (blockSum_inj.mp h).1
/-- Lower-right corner inclusion `N ↦ blockSum 0 N` as a non-unital `⋆`-algebra homomorphism. -/
def inrNonUnitalStarAlgHom (R m : Type*) [Semiring R] [Fintype m] [Module R A] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (m ⊕ n) (m ⊕ n) A :=
  (blockSumNonUnitalStarAlgHom R).comp (.inr R _ _)
@[simp low] theorem inrNonUnitalStarAlgHom_apply (N : CStarMatrix n n A) :
    inrNonUnitalStarAlgHom R m N = blockSum 0 N := (rfl)
/-- The lower-right corner inclusion `inrNonUnitalStarAlgHom` is injective. -/
theorem inrNonUnitalStarAlgHom_injective : Function.Injective
    (inrNonUnitalStarAlgHom R m (n := n) (A := A)) := fun _ _ h => (blockSum_inj.mp h).2
end
end Blocks

section Amplify
variable {k k₁ k₂ l m m₁ m₂ n n₁ n₂ R A B : Type*}
/-- Block-diagonal amplification `1_k ⊗ M` of `M : CStarMatrix m n A` along index type `k`. -/
def amplify (k : Type*) [DecidableEq k] [Zero A] (M : CStarMatrix m n A) :
    CStarMatrix (k × m) (k × n) A := ofMatrix (Matrix.reindex (.prodComm m k) (.prodComm n k)
  (Matrix.blockDiagonal fun _ : k => ofMatrix.symm M))
variable [DecidableEq k]
section
variable (M : CStarMatrix m n A)
@[simp] theorem ofMatrix_symm_amplify [Zero A] : ofMatrix.symm (amplify k M) =
    Matrix.reindex (.prodComm m k) (.prodComm n k)
      (Matrix.blockDiagonal fun _ : k => ofMatrix.symm M) := (rfl)
@[simp] theorem amplify_apply [Zero A] (i : k × m) (j : k × n) :
    amplify k M i j = if i.1 = j.1 then M i.2 j.2 else 0 := (rfl)
@[simp] theorem amplify_of_isEmpty [IsEmpty k] [Zero A] : amplify k M = 0 := Subsingleton.elim _ _
@[simp] theorem amplify_neg [NegZeroClass A] : -amplify k M = amplify k (-M) := by
  ext i j; by_cases h : i.1 = j.1 <;> simp [h]
@[simp] theorem amplify_conjTranspose [AddMonoid A] [StarAddMonoid A] :
    (amplify k M).conjTranspose = amplify k M.conjTranspose := by
  ext ⟨i₁, _⟩ ⟨j₁, _⟩; by_cases h : i₁ = j₁ <;> simp [h, eq_comm]
@[simp] theorem map_amplify [Zero A] [Zero B] {f : A → B} (hf : f 0 = 0) :
    (amplify k M).map f = amplify k (M.map f) := by ext i j; by_cases h : i.1 = j.1 <;> simp [h, hf]
end
@[simp] theorem amplify_zero [Zero A] : amplify k (0 : CStarMatrix m n A) = 0 := by ext; simp
@[simp] theorem amplify_one [DecidableEq n] [Zero A] [One A] :
    amplify k (1 : CStarMatrix n n A) = 1 := by
  ext ⟨_, _⟩ ⟨_, _⟩; simp [one_apply, Prod.ext_iff, ite_and]
@[simp] theorem amplify_add [AddZeroClass A] (M N : CStarMatrix m n A) :
    amplify k M + amplify k N = amplify k (M + N) := by ext i j; by_cases h : i.1 = j.1 <;> simp [h]
@[simp] theorem amplify_sub [SubNegZeroMonoid A] (M N : CStarMatrix m n A) :
    amplify k M - amplify k N = amplify k (M - N) := by ext i j; by_cases h : i.1 = j.1 <;> simp [h]
@[simp] theorem amplify_smul [Zero A] [SMulZeroClass R A] (r : R) (M : CStarMatrix m n A) :
    r • amplify k M = amplify k (r • M) := by ext i j; by_cases h : i.1 = j.1 <;> simp [h]
@[simp] theorem amplify_mul [Fintype k] [Fintype m] [NonUnitalNonAssocSemiring A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    amplify k M * amplify k N = amplify k (M * N) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [mul_apply, amplify_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i₁]
  · simp
  · intro b _ hb
    simp [hb.symm]
  · simp
@[simp] theorem amplify_pow [Fintype k] [Fintype n] [DecidableEq n] [Semiring A]
    (M : CStarMatrix n n A) (r : ℕ) : amplify k M ^ r = amplify k (M ^ r) := by
  induction r with | zero => simp | succ r ih => rw [pow_succ, ih, amplify_mul, pow_succ]
@[simp] theorem star_amplify [AddMonoid A] [StarAddMonoid A] (M : CStarMatrix n n A) :
    star (amplify k M) = amplify k (star M) := amplify_conjTranspose M
/-- Finite block-diagonal amplification over a nonempty index type `k` is injective. -/
theorem amplify_injective [Nonempty k] [Zero A] :
    Function.Injective (amplify k : CStarMatrix m n A → CStarMatrix (k × m) (k × n) A) :=
  fun _ _ h => let ⟨x⟩ := ‹Nonempty k›; ext fun i j => by
    simpa using congr_fun (congr_fun h (x, i)) (x, j)
@[simp] theorem amplify_inj [Nonempty k] [Zero A] {M N : CStarMatrix m n A} :
    amplify k M = amplify k N ↔ M = N := (amplify_injective (k := k)).eq_iff
@[simp] theorem amplify_eq_zero_iff [Nonempty k] [Zero A] {M : CStarMatrix m n A} :
    amplify k M = 0 ↔ M = 0 := by rw [← amplify_zero, amplify_inj]
section
variable {P : CStarMatrix n n A}
@[simp] theorem isIdempotentElem_amplify_iff [Fintype k] [Nonempty k] [Fintype n]
    [NonUnitalNonAssocSemiring A] :
    IsIdempotentElem (amplify k P) ↔ IsIdempotentElem P := by simp [IsIdempotentElem]
@[simp] theorem isSelfAdjoint_amplify_iff [Nonempty k] [AddMonoid A] [StarAddMonoid A] :
    IsSelfAdjoint (amplify k P) ↔ IsSelfAdjoint P := by simp [IsSelfAdjoint]
/-- Finite block-diagonal amplification preserves star projections. -/
theorem _root_.IsStarProjection.amplify (k : Type*) [Fintype k] [DecidableEq k] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A] (hP : IsStarProjection P) :
    IsStarProjection (CStarMatrix.amplify k P) :=
  ⟨by rw [IsIdempotentElem, amplify_mul, hP.isIdempotentElem.eq],
    by rw [IsSelfAdjoint, star_amplify, hP.isSelfAdjoint.star_eq]⟩
@[simp] theorem isStarProjection_amplify_iff [Fintype k] [Nonempty k] [Fintype n]
    [NonUnitalNonAssocSemiring A] [StarAddMonoid A] :
    IsStarProjection (amplify k P) ↔ IsStarProjection P := by simp [isStarProjection_iff]
end
section
variable [Semiring R] [AddCommMonoid A] [Module R A]
@[simp] theorem reindexₗ_uniqueProd_amplify [Unique k] (M : CStarMatrix m n A) :
    reindexₗ R A (Equiv.uniqueProd m k) (Equiv.uniqueProd n k) (amplify k M) = M := by
  ext i j; simp [Matrix.reindex, Matrix.submatrix]
@[simp] theorem reindexₐ_uniqueProd_amplify [Fintype k] [Unique k] [Fintype m] [Mul A] [Star A]
    (M : CStarMatrix m m A) : reindexₐ R A (Equiv.uniqueProd m k) (amplify k M) = M :=
  (reindexₗ_self_eq_reindexₐ ..).symm.trans (reindexₗ_uniqueProd_amplify M)
section
variable [DecidableEq k₁] [DecidableEq k₂]
@[simp] theorem reindexₗ_prodCongr_amplify (eₖ : k₁ ≃ k₂) (eₘ : m₁ ≃ m₂) (eₙ : n₁ ≃ n₂)
    (M : CStarMatrix m₁ n₁ A) : reindexₗ R A (Equiv.prodCongr eₖ eₘ) (Equiv.prodCongr eₖ eₙ)
      (amplify k₁ M) = amplify k₂ (reindexₗ R A eₘ eₙ M) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩; simp [Matrix.reindex, Matrix.submatrix]
@[simp] theorem reindexₗ_prodAssoc_amplify (M : CStarMatrix m n A) :
    reindexₗ R A (Equiv.prodAssoc k₁ k₂ m) (Equiv.prodAssoc k₁ k₂ n) (amplify (k₁ × k₂) M) =
      amplify k₁ (amplify k₂ M) := by
  ext ⟨i₁, i₂, i₃⟩ ⟨j₁, j₂, j₃⟩; simp [Matrix.reindex, Matrix.submatrix, Prod.ext_iff, ite_and]
@[simp] theorem reindexₗ_sumProdDistrib_amplify (M : CStarMatrix m n A) :
    reindexₗ R A (Equiv.sumProdDistrib k₁ k₂ m) (Equiv.sumProdDistrib k₁ k₂ n)
      (amplify (k₁ ⊕ k₂) M) = blockSum (amplify k₁ M) (amplify k₂ M) := by
  ext (⟨i₁, i₂⟩ | ⟨i₁, i₂⟩) (⟨j₁, j₂⟩ | ⟨j₁, j₂⟩) <;> simp [Matrix.reindex, Matrix.submatrix]
section
variable [Fintype k₁] [Fintype k₂] [Fintype m] [Mul A] [Star A]
@[simp] theorem reindexₐ_prodCongr_amplify [Fintype n] (eₖ : k₁ ≃ k₂) (e : m ≃ n)
    (M : CStarMatrix m m A) : reindexₐ R A (.prodCongr eₖ e) (amplify k₁ M) =
      amplify k₂ (reindexₐ R A e M) := by
  rw [← reindexₗ_self_eq_reindexₐ, ← reindexₗ_self_eq_reindexₐ]; exact reindexₗ_prodCongr_amplify ..
@[simp] theorem reindexₐ_prodAssoc_amplify (M : CStarMatrix m m A) :
    reindexₐ R A (Equiv.prodAssoc k₁ k₂ m) (amplify (k₁ × k₂) M) = amplify k₁ (amplify k₂ M) :=
  (reindexₗ_self_eq_reindexₐ ..).symm.trans (reindexₗ_prodAssoc_amplify M)
@[simp] theorem reindexₐ_sumProdDistrib_amplify (M : CStarMatrix m m A) :
    reindexₐ R A (Equiv.sumProdDistrib k₁ k₂ m) (amplify (k₁ ⊕ k₂) M) =
      blockSum (amplify k₁ M) (amplify k₂ M) :=
  (reindexₗ_self_eq_reindexₐ ..).symm.trans (reindexₗ_sumProdDistrib_amplify M)
end
end
end
section
variable [Fintype n] [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
/-- Finite block-diagonal amplification bundled as a non-unital `⋆`-algebra homomorphism. -/
def amplifyNonUnitalStarAlgHom (R k : Type*) [Fintype k] [DecidableEq k] [Semiring R] [Module R A] :
    CStarMatrix n n A →⋆ₙₐ[R] CStarMatrix (k × n) (k × n) A :=
  { toFun := amplify k, map_smul' := fun r M => (amplify_smul r M).symm, map_zero' := amplify_zero,
    map_add' := fun M N => (amplify_add M N).symm, map_mul' := fun M N => (amplify_mul M N).symm,
    map_star' := fun M => (star_amplify M).symm }
variable [Fintype k] [Semiring R] [Module R A]
@[simp low] theorem amplifyNonUnitalStarAlgHom_apply (M : CStarMatrix n n A) :
    amplifyNonUnitalStarAlgHom R k M = amplify k M := (rfl)
/-- `amplifyNonUnitalStarAlgHom` over a nonempty index type `k` is injective. -/
theorem amplifyNonUnitalStarAlgHom_injective [Nonempty k] :
    Function.Injective (amplifyNonUnitalStarAlgHom R k (n := n) (A := A)) := amplify_injective
end
section
variable [Fintype n] [DecidableEq n] [Semiring A] [StarAddMonoid A]
/-- Unital finite block-diagonal amplification bundled as a `⋆`-algebra homomorphism. -/
def amplifyStarAlgHom (R k : Type*) [Fintype k] [DecidableEq k] [CommSemiring R] [Algebra R A] :
    CStarMatrix n n A →⋆ₐ[R] CStarMatrix (k × n) (k × n) A := { amplifyNonUnitalStarAlgHom R k with
  map_one' := amplify_one
  commutes' r := by ext ⟨_, _⟩ ⟨_, _⟩; simp [algebraMap_apply, Prod.ext_iff, ite_and] }
variable [Fintype k] [CommSemiring R] [Algebra R A]
@[simp low] theorem amplifyStarAlgHom_apply (M : CStarMatrix n n A) :
    amplifyStarAlgHom R k M = amplify k M := (rfl)
/-- `amplifyStarAlgHom` over a nonempty index type `k` is injective. -/
theorem amplifyStarAlgHom_injective [Nonempty k] :
    Function.Injective (amplifyStarAlgHom R k (n := n) (A := A)) := amplify_injective
end
end Amplify

section Norms
open WithCStarModule
open scoped InnerProductSpace WithCStarModule
variable {k l m n o A : Type*} [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]
section
variable [Fintype l] [Fintype o]
/-- The operator norm of a block-diagonal `CStarMatrix` is the maximum of its block norms. -/
@[simp] theorem norm_blockSum (M : CStarMatrix m l A) (N : CStarMatrix o n A) :
    ‖blockSum M N‖ = max ‖M‖ ‖N‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (le_max_of_le_left (norm_nonneg M))).mp <| by
    have hsq := NonUnitalStarAlgHom.norm_map
      (blockSumNonUnitalStarAlgHom ℂ (m := l) (n := n) (A := A))
      blockSumNonUnitalStarAlgHom_injective (M.conjTranspose * M, N.conjTranspose * N)
    rw [blockSumNonUnitalStarAlgHom_apply, Prod.norm_def] at hsq
    rw [← norm_conjTranspose_mul_self, blockSum_conjTranspose, blockSum_mul, hsq,
      norm_conjTranspose_mul_self, norm_conjTranspose_mul_self]
    exact (max_pow_of_nonneg (norm_nonneg M) (norm_nonneg N) 2).symm
section
variable (M : CStarMatrix (m ⊕ o) (l ⊕ n) A)
/-- Extracting the upper-left block does not increase the operator norm. -/
theorem norm_toBlocks₁₁_le : ‖M.toBlocks₁₁‖ ≤ ‖M‖ := by
  refine norm_le_of_forall_inner_le (C := ‖M‖₊) fun v w => ?_
  let v' : C⋆ᵐᵒᵈ(A, m ⊕ o → A) := (equiv A _).symm (Sum.elim (equiv A _ v) 0)
  let w' : C⋆ᵐᵒᵈ(A, l ⊕ n → A) := (equiv A _).symm (Sum.elim (equiv A _ w) 0)
  have hv' : ‖v'‖ = ‖v‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
    simp [CStarModule.norm_sq_eq A, pi_inner, inner_def, v']
  have hw' : ‖w'‖ = ‖w‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
    simp [CStarModule.norm_sq_eq A, pi_inner, inner_def, w']
  have hinner : ⟪w', toCLM M v'⟫_A = ⟪w, toCLM M.toBlocks₁₁ v⟫_A := by
    simp [pi_inner, inner_def, toCLM_apply_eq_sum, v', w', toBlocks₁₁_apply]
  have hle : ‖⟪w', toCLM M v'⟫_A‖ ≤ ‖w'‖ * (‖toCLM M‖ * ‖v'‖) :=
    (CStarModule.norm_inner_le _).trans (by gcongr; exact (toCLM M).le_opNorm _)
  simpa [hinner, ← norm_def, hv', hw', mul_assoc, mul_left_comm, mul_comm] using hle
/-- Extracting the upper-right block does not increase the operator norm. -/
theorem norm_toBlocks₁₂_le : ‖M.toBlocks₁₂‖ ≤ ‖M‖ := by
  have h : M.toBlocks₁₂ = (reindexₗ ℂ A (.refl _) (.sumComm l n) M).toBlocks₁₁ := by
    ext i j
    simp [toBlocks₁₂_apply, toBlocks₁₁_apply, reindexₗ_apply]; rfl
  rw [h]
  exact (norm_toBlocks₁₁_le _).trans_eq (norm_reindexₗ ..)
/-- Extracting the lower-left block does not increase the operator norm. -/
theorem norm_toBlocks₂₁_le : ‖M.toBlocks₂₁‖ ≤ ‖M‖ := by
  have h : M.toBlocks₂₁ = (reindexₗ ℂ A (.sumComm m o) (.refl _) M).toBlocks₁₁ := by
    ext i j
    simp [toBlocks₂₁_apply, toBlocks₁₁_apply, reindexₗ_apply]; rfl
  rw [h]
  exact (norm_toBlocks₁₁_le _).trans_eq (norm_reindexₗ ..)
/-- Extracting the lower-right block does not increase the operator norm. -/
theorem norm_toBlocks₂₂_le : ‖M.toBlocks₂₂‖ ≤ ‖M‖ := by
  have h : M.toBlocks₂₂ = (reindexₗ ℂ A (.sumComm m o) (.sumComm l n) M).toBlocks₁₁ := by
    ext i j
    simp [toBlocks₂₂_apply, toBlocks₁₁_apply, reindexₗ_apply]; rfl
  rw [h]
  exact (norm_toBlocks₁₁_le _).trans_eq (norm_reindexₗ ..)
end
/-- Operator norm bound for a four-block `CStarMatrix` via its diagonal and off-diagonal blocks. -/
theorem norm_fromBlocks_le (M₁₁ : CStarMatrix m l A) (M₁₂ : CStarMatrix m n A)
    (M₂₁ : CStarMatrix o l A) (M₂₂ : CStarMatrix o n A) :
    ‖fromBlocks M₁₁ M₁₂ M₂₁ M₂₂‖ ≤ max ‖M₁₁‖ ‖M₂₂‖ + max ‖M₁₂‖ ‖M₂₁‖ := by
  rw [fromBlocks_eq_blockSum_add_reindexₗ ℂ M₁₁ M₁₂ M₂₁ M₂₂]
  exact (norm_add_le _ _).trans (by simp [norm_reindexₗ])
end
/-- Finite block-diagonal amplification over a nonempty index type `k` is isometric. -/
@[simp] theorem norm_amplify [Fintype k] [DecidableEq k] [Nonempty k] (M : CStarMatrix m n A) :
    ‖amplify k M‖ = ‖M‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
  rw [← norm_conjTranspose_mul_self, amplify_conjTranspose, amplify_mul,
    ← amplifyNonUnitalStarAlgHom_apply (R := ℂ), NonUnitalStarAlgHom.norm_map
      (amplifyNonUnitalStarAlgHom ℂ k (n := n) (A := A)) amplifyNonUnitalStarAlgHom_injective _,
    norm_conjTranspose_mul_self]
/-- Finite block-diagonal amplification over any finite index type `k` is contractive. -/
theorem norm_amplify_le [Fintype k] [DecidableEq k] (M : CStarMatrix m n A) : ‖amplify k M‖ ≤ ‖M‖ :=
  (isEmpty_or_nonempty k).elim (fun _ => by rw [amplify_of_isEmpty, norm_zero]; exact norm_nonneg M)
    fun _ => (norm_amplify M).le
end Norms

section Continuity
variable {k l m n o X A : Type*} [TopologicalSpace X] [NonUnitalCStarAlgebra A]
/-- A four-block `CStarMatrix` family is continuous when each of its four blocks is continuous. -/
@[fun_prop] theorem continuous_fromBlocks {f₁₁ : X → CStarMatrix m l A}
    {f₁₂ : X → CStarMatrix m n A} {f₂₁ : X → CStarMatrix o l A} {f₂₂ : X → CStarMatrix o n A}
    (hf₁₁ : Continuous f₁₁) (hf₁₂ : Continuous f₁₂) (hf₂₁ : Continuous f₂₁)
    (hf₂₂ : Continuous f₂₂) : Continuous fun x => fromBlocks (f₁₁ x) (f₁₂ x) (f₂₁ x) (f₂₂ x) :=
  continuous_ofMatrix.comp <| Continuous.matrix_fromBlocks
    (continuous_ofMatrix_symm.comp hf₁₁) (continuous_ofMatrix_symm.comp hf₁₂)
    (continuous_ofMatrix_symm.comp hf₂₁) (continuous_ofMatrix_symm.comp hf₂₂)
section
variable {f : X → CStarMatrix (m ⊕ o) (l ⊕ n) A} (hf : Continuous f)
include hf
/-- Extracting the upper-left block `toBlocks₁₁` of a continuous family is continuous. -/
@[fun_prop] theorem continuous_toBlocks₁₁ : Continuous fun x => (f x).toBlocks₁₁ :=
  continuous_ofMatrix.comp <| (continuous_ofMatrix_symm.comp hf).matrix_submatrix .inl .inl
/-- Extracting the upper-right block `toBlocks₁₂` of a continuous family is continuous. -/
@[fun_prop] theorem continuous_toBlocks₁₂ : Continuous fun x => (f x).toBlocks₁₂ :=
  continuous_ofMatrix.comp <| (continuous_ofMatrix_symm.comp hf).matrix_submatrix .inl .inr
/-- Extracting the lower-left block `toBlocks₂₁` of a continuous family is continuous. -/
@[fun_prop] theorem continuous_toBlocks₂₁ : Continuous fun x => (f x).toBlocks₂₁ :=
  continuous_ofMatrix.comp <| (continuous_ofMatrix_symm.comp hf).matrix_submatrix .inr .inl
/-- Extracting the lower-right block `toBlocks₂₂` of a continuous family is continuous. -/
@[fun_prop] theorem continuous_toBlocks₂₂ : Continuous fun x => (f x).toBlocks₂₂ :=
  continuous_ofMatrix.comp <| (continuous_ofMatrix_symm.comp hf).matrix_submatrix .inr .inr
end
/-- A row-stacked `CStarMatrix` family is continuous when both row blocks are continuous. -/
@[fun_prop] theorem continuous_fromRows {f₁ : X → CStarMatrix m l A} {f₂ : X → CStarMatrix o l A}
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) : Continuous fun x => fromRows (f₁ x) (f₂ x) :=
  continuous_iff.mpr fun i j => match i with
    | .inl i => by simpa only [fromRows_apply_inl] using continuous_iff.mp hf₁ i j
    | .inr i => by simpa only [fromRows_apply_inr] using continuous_iff.mp hf₂ i j
/-- A block-diagonal `CStarMatrix` family is continuous when both diagonal blocks are continuous. -/
@[fun_prop] theorem continuous_blockSum {f : X → CStarMatrix m l A} {g : X → CStarMatrix o n A}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => blockSum (f x) (g x) :=
  continuous_fromBlocks hf continuous_const continuous_const hg
/-- Finite block-diagonal amplification of a continuous `CStarMatrix` family is continuous. -/
@[fun_prop] theorem continuous_amplify [DecidableEq k] {f : X → CStarMatrix m n A}
    (hf : Continuous f) : Continuous fun x => amplify k (f x) :=
  continuous_ofMatrix.comp <|
    (Continuous.matrix_blockDiagonal (continuous_pi fun _ : k =>
      continuous_ofMatrix_symm.comp hf)).matrix_submatrix _ _
end Continuity
end CStarMatrix
