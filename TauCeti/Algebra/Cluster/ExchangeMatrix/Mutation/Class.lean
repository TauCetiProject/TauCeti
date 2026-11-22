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

The projection and realization use `TauCeti.matrixMutationWord_fromBlocks` and its
`_inl` and `_inr` specializations in `ExchangeMatrix.Word`. For rectangular matrices,
the uniform product bound on principal entries holds exactly when it holds in each block.
This reduces the product-bound part of two-finiteness to components; for skew-symmetrizable
exchange matrices the sign condition is already ensured. These statements concern matrix
mutation classes,
not finiteness of the set of cluster variables. They allow empty and infinite index types
and do not require skew-symmetrizability.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras II: Finite type classification*,
  Inventiones Mathematicae 154 (2003), Theorems 1.8 and 7.1.
-/

public section

open TauCeti

namespace Function.Embedding

variable {I₁ I₂ K₁ K₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]
  [DecidableEq K₁] [DecidableEq K₂]
  (row₁ : K₁ ↪ I₁) (row₂ : K₂ ↪ I₂) (B₁ : Matrix I₁ K₁ ℤ) (B₂ : Matrix I₂ K₂ ℤ)

omit [DecidableEq I₁] [DecidableEq I₂] [DecidableEq K₁] [DecidableEq K₂] in
private theorem blockConstructor_injective : Function.Injective
    (fun p : Matrix I₁ K₁ ℤ × Matrix I₂ K₂ ℤ ↦ Matrix.fromBlocks p.1 0 0 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simpa only [Matrix.fromBlocks_inj, and_true, true_and, Prod.mk.injEq] using h

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
@[simp]
theorem finite_range_matrixMutationWord_fromBlocks_iff :
    (Set.range (matrixMutationWord (row₁.sumMap row₂)
      (Matrix.fromBlocks B₁ 0 0 B₂))).Finite ↔
      (Set.range (matrixMutationWord row₁ B₁)).Finite ∧
        (Set.range (matrixMutationWord row₂ B₂)).Finite := by
  rw [row₁.range_matrixMutationWord_fromBlocks row₂ B₁ B₂,
    Set.finite_image_iff blockConstructor_injective.injOn, Set.finite_prod]
  simp only [(Set.range_nonempty (matrixMutationWord row₁ B₁)).ne_empty,
    (Set.range_nonempty (matrixMutationWord row₂ B₂)).ne_empty, or_false]

/-- Extended cardinality of a block mutation class is the product of its component
cardinalities, retaining infinite values. -/
@[simp]
theorem encard_range_matrixMutationWord_fromBlocks :
    (Set.range (matrixMutationWord (row₁.sumMap row₂)
      (Matrix.fromBlocks B₁ 0 0 B₂))).encard =
      (Set.range (matrixMutationWord row₁ B₁)).encard *
        (Set.range (matrixMutationWord row₂ B₂)).encard := by
  rw [row₁.range_matrixMutationWord_fromBlocks row₂ B₁ B₂,
    blockConstructor_injective.encard_image, Set.encard_prod]

/-- Natural cardinality of a block mutation class is the product of its component
cardinalities, with Mathlib's zero convention for infinite sets. -/
@[simp]
theorem ncard_range_matrixMutationWord_fromBlocks :
    (Set.range (matrixMutationWord (row₁.sumMap row₂)
      (Matrix.fromBlocks B₁ 0 0 B₂))).ncard =
      (Set.range (matrixMutationWord row₁ B₁)).ncard *
        (Set.range (matrixMutationWord row₂ B₂)).ncard := by
  simpa only [Set.ncard_def, ENat.toNat_mul] using
    congrArg ENat.toNat (row₁.encard_range_matrixMutationWord_fromBlocks row₂ B₁ B₂)

end Function.Embedding

namespace Matrix

variable {I₁ I₂ K₁ K₂ : Type*} [DecidableEq I₁] [DecidableEq I₂]
  [DecidableEq K₁] [DecidableEq K₂]

/-- A nonnegative uniform bound on principal entry products in a rectangular block
mutation class holds exactly when it holds in both components. Bound three is the
product-bound part of two-finiteness, with its sign condition supplied by skew-symmetrizability. -/
theorem forall_abs_matrixMutationWord_mul_le_fromBlocks_iff
    (B₁ : Matrix I₁ K₁ ℤ) (row₁ : K₁ ↪ I₁) (row₂ : K₂ ↪ I₂)
    (B₂ : Matrix I₂ K₂ ℤ) (bound : ℤ) (hbound : 0 ≤ bound) :
    (∀ w : List (K₁ ⊕ K₂), ∀ i j, i ≠ j →
      |matrixMutationWord (row₁.sumMap row₂) (fromBlocks B₁ 0 0 B₂) w
          ((row₁.sumMap row₂) i) j *
        matrixMutationWord (row₁.sumMap row₂) (fromBlocks B₁ 0 0 B₂) w
          ((row₁.sumMap row₂) j) i| ≤ bound) ↔
      (∀ w : List K₁, ∀ i j, i ≠ j →
        |matrixMutationWord row₁ B₁ w (row₁ i) j *
          matrixMutationWord row₁ B₁ w (row₁ j) i| ≤ bound) ∧
      (∀ w : List K₂, ∀ i j, i ≠ j →
        |matrixMutationWord row₂ B₂ w (row₂ i) j *
          matrixMutationWord row₂ B₂ w (row₂ j) i| ≤ bound) := by
  have hp (C₁ : Matrix I₁ K₁ ℤ) (C₂ : Matrix I₂ K₂ ℤ) :
      (∀ i j, i ≠ j → |fromBlocks C₁ 0 0 C₂ ((row₁.sumMap row₂) i) j *
        fromBlocks C₁ 0 0 C₂ ((row₁.sumMap row₂) j) i| ≤ bound) ↔
      (∀ i j, i ≠ j → |C₁ (row₁ i) j * C₁ (row₁ j) i| ≤ bound) ∧
        (∀ i j, i ≠ j → |C₂ (row₂ i) j * C₂ (row₂ j) i| ≤ bound) := by
    simp only [Function.Embedding.coe_sumMap]
    constructor
    · intro h
      exact ⟨fun i j hij ↦ by simpa using h (.inl i) (.inl j) (by simpa using hij),
        fun i j hij ↦ by simpa using h (.inr i) (.inr j) (by simpa using hij)⟩
    · rintro ⟨h₁, h₂⟩ (i | i) (j | j) hij
      · simpa only [Sum.map_inl, fromBlocks_apply₁₁] using h₁ i j (by simpa using hij)
      · simpa using hbound
      · simpa using hbound
      · simpa only [Sum.map_inr, fromBlocks_apply₂₂] using h₂ i j (by simpa using hij)
  rw [← Set.forall_mem_range
    (f := matrixMutationWord (row₁.sumMap row₂) (fromBlocks B₁ 0 0 B₂))
    (p := fun C : Matrix (I₁ ⊕ I₂) (K₁ ⊕ K₂) ℤ ↦ ∀ i j, i ≠ j →
      |C ((row₁.sumMap row₂) i) j * C ((row₁.sumMap row₂) j) i| ≤ bound)]
  rw [row₁.range_matrixMutationWord_fromBlocks row₂ B₁ B₂,
    Set.forall_mem_image, Set.forall_prod_set]
  simp_rw [hp]
  rw [← Set.forall_mem_range (f := matrixMutationWord row₁ B₁)
    (p := fun C : Matrix I₁ K₁ ℤ ↦ ∀ i j, i ≠ j → |C (row₁ i) j * C (row₁ j) i| ≤ bound),
    ← Set.forall_mem_range (f := matrixMutationWord row₂ B₂)
    (p := fun C : Matrix I₂ K₂ ℤ ↦ ∀ i j, i ≠ j → |C (row₂ i) j * C (row₂ j) i| ≤ bound)]
  obtain ⟨C₁, hC₁⟩ := Set.range_nonempty (matrixMutationWord row₁ B₁)
  obtain ⟨C₂, hC₂⟩ := Set.range_nonempty (matrixMutationWord row₂ B₂)
  exact ⟨fun h ↦ ⟨fun C hC ↦ (h C hC C₂ hC₂).1, fun C hC ↦ (h C₁ hC₁ C hC).2⟩,
    fun ⟨h₁, h₂⟩ C hC D hD ↦ ⟨h₁ C hC, h₂ D hD⟩⟩

end Matrix
