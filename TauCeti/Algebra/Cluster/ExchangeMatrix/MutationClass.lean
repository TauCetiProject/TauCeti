/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Word
public import Mathlib.Data.Set.Card

/-!
# Mutation classes of block diagonal matrices

The full mutation class of a block diagonal matrix is the product of the mutation classes
of its blocks, embedded by the block diagonal construction. Arbitrary interleaved words
project to words in the two blocks; conversely any pair of block words can be realized by
concatenating their inclusions. Consequently the full class is finite exactly when both
component classes are finite, and its cardinality is their product.

For square matrices, the uniform off-diagonal product bound in the two-finite criterion
holds exactly when it holds in each block. This reduces the disconnected part of the
matrix classification to its components. These statements concern matrix mutation classes,
not finiteness of the set of cluster variables. They allow empty and infinite index types
and do not require skew-symmetrizability.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras II: Finite type classification*,
  Inventiones Mathematicae 154 (2003), Theorems 1.8 and 7.1.
-/

public section

namespace TauCeti

section Rectangular

variable {I₁ I₂ K₁ K₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]
  [DecidableEq K₁] [DecidableEq K₂]
  (row₁ : K₁ ↪ I₁) (row₂ : K₂ ↪ I₂) (B₁ : Matrix I₁ K₁ ℤ) (B₂ : Matrix I₂ K₂ ℤ)

/-- The full mutation class of a block sum realizes every pair of component mutations. -/
theorem range_matrixMutationWord_fromBlocks :
    Set.range (matrixMutationWord (row₁.sumMap row₂) (Matrix.fromBlocks B₁ 0 0 B₂)) =
      (fun p : Matrix I₁ K₁ ℤ × Matrix I₂ K₂ ℤ ↦ Matrix.fromBlocks p.1 0 0 p.2) ''
        (Set.range (matrixMutationWord row₁ B₁) ×ˢ Set.range (matrixMutationWord row₂ B₂)) := by
  ext C
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨(matrixMutationWord row₁ B₁ (w.filterMap Sum.getLeft?),
      matrixMutationWord row₂ B₂ (w.filterMap Sum.getRight?)),
      ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩, ?_⟩
    exact (matrixMutationWord_fromBlocks row₁ row₂ B₁ B₂ w).symm
  · rintro ⟨⟨C₁, C₂⟩, ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩, rfl⟩
    refine ⟨u.map Sum.inl ++ v.map Sum.inr, ?_⟩
    rw [matrixMutationWord_append, matrixMutationWord_fromBlocks_inl,
      matrixMutationWord_fromBlocks_inr]

/-- A block sum has a finite mutation class exactly when both component classes are finite. -/
theorem finite_range_matrixMutationWord_fromBlocks_iff :
    (Set.range (matrixMutationWord (row₁.sumMap row₂)
      (Matrix.fromBlocks B₁ 0 0 B₂))).Finite ↔
      (Set.range (matrixMutationWord row₁ B₁)).Finite ∧
        (Set.range (matrixMutationWord row₂ B₂)).Finite := by
  rw [range_matrixMutationWord_fromBlocks]
  have hi : Function.Injective
      (fun p : Matrix I₁ K₁ ℤ × Matrix I₂ K₂ ℤ ↦ Matrix.fromBlocks p.1 0 0 p.2) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simpa only [Matrix.fromBlocks_inj, and_true, true_and, Prod.mk.injEq] using h
  rw [Set.finite_image_iff hi.injOn, Set.finite_prod]
  have h₁ : (Set.range (matrixMutationWord row₁ B₁)).Nonempty :=
    ⟨_, [], matrixMutationWord_nil _ _⟩
  have h₂ : (Set.range (matrixMutationWord row₂ B₂)).Nonempty :=
    ⟨_, [], matrixMutationWord_nil _ _⟩
  simp only [h₁.ne_empty, h₂.ne_empty, or_false]

/-- The cardinality of a block mutation class is the product of the component cardinalities.
As for Set.ncard, an infinite mutation class has cardinality zero in this formula. -/
theorem ncard_range_matrixMutationWord_fromBlocks :
    (Set.range (matrixMutationWord (row₁.sumMap row₂)
      (Matrix.fromBlocks B₁ 0 0 B₂))).ncard =
      (Set.range (matrixMutationWord row₁ B₁)).ncard *
        (Set.range (matrixMutationWord row₂ B₂)).ncard := by
  rw [range_matrixMutationWord_fromBlocks, ← Set.ncard_prod]
  apply Set.InjOn.ncard_image
  rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h
  simpa only [Matrix.fromBlocks_inj, and_true, true_and, Prod.mk.injEq] using h

end Rectangular

section Square

variable {K₁ K₂ : Type*} [DecidableEq K₁] [DecidableEq K₂]
  (B₁ : Matrix K₁ K₁ ℤ) (B₂ : Matrix K₂ K₂ ℤ)

/-- A nonnegative uniform bound on off-diagonal entry products holds throughout a block
mutation class exactly when it holds throughout both component classes. In particular,
bound three gives the componentwise two-finiteness criterion. -/
theorem forall_abs_matrixMutationWord_mul_le_fromBlocks_iff (bound : ℤ) (hbound : 0 ≤ bound) :
    (∀ w : List (K₁ ⊕ K₂), ∀ i j, i ≠ j →
      |matrixMutationWord (Function.Embedding.refl (K₁ ⊕ K₂))
          (Matrix.fromBlocks B₁ 0 0 B₂) w i j *
        matrixMutationWord (Function.Embedding.refl (K₁ ⊕ K₂))
          (Matrix.fromBlocks B₁ 0 0 B₂) w j i| ≤ bound) ↔
      (∀ w : List K₁, ∀ i j, i ≠ j →
        |matrixMutationWord (Function.Embedding.refl K₁) B₁ w i j *
          matrixMutationWord (Function.Embedding.refl K₁) B₁ w j i| ≤ bound) ∧
      (∀ w : List K₂, ∀ i j, i ≠ j →
        |matrixMutationWord (Function.Embedding.refl K₂) B₂ w i j *
          matrixMutationWord (Function.Embedding.refl K₂) B₂ w j i| ≤ bound) := by
  have hr : (Function.Embedding.refl K₁).sumMap (Function.Embedding.refl K₂) =
      Function.Embedding.refl (K₁ ⊕ K₂) := by
    ext k
    cases k <;> rfl
  rw [← hr]
  constructor
  · intro h
    constructor
    · intro w i j hij
      have hw := h (w.map Sum.inl) (Sum.inl i) (Sum.inl j) (by simpa using hij)
      simpa only [matrixMutationWord_fromBlocks_inl, Matrix.fromBlocks_apply₁₁] using hw
    · intro w i j hij
      have hw := h (w.map Sum.inr) (Sum.inr i) (Sum.inr j) (by simpa using hij)
      simpa only [matrixMutationWord_fromBlocks_inr, Matrix.fromBlocks_apply₂₂] using hw
  · rintro ⟨h₁, h₂⟩ w i j hij
    rw [matrixMutationWord_fromBlocks]
    cases i with
    | inl i =>
      cases j with
      | inl j => exact h₁ _ i j (by simpa using hij)
      | inr j => simpa using hbound
    | inr i =>
      cases j with
      | inl j => simpa using hbound
      | inr j => exact h₂ _ i j (by simpa using hij)

end Square

end TauCeti
