/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Basic

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Matrix mutation

Mutation in direction `k` is the operation on exchange matrices that underlies every cluster
exchange. For an integer matrix `B` with rows `I` and columns `K`, and an embedding
`row : K ↪ I` of the mutable indices, the mutated matrix `B'` has entries

* `B' i j = -B i j` if `i = row k` or `j = k`,
* `B' i j = B i j + [B i k]₊ * [B (row k) j]₊ - [-B i k]₊ * [-B (row k) j]₊` otherwise,

where `[a]₊ = max a 0`, written `a⁺` below, and `[-a]₊` is `a⁻`. The same formula is used on the
mutable and on the frozen rows; a square matrix is mutated along `Function.Embedding.refl K`.

This file defines the operation on plain matrices, proves that it is an involution and that it
commutes with negation, with passage to submatrices (in particular to the principal block and
along reindexing), and with block diagonal sums. It then shows that a skew-symmetrizer of a
square matrix is still one after mutation, so mutation acts on exchange matrices.

## Main definitions

* `TauCeti.matrixMutation row B k`: the mutation of the matrix `B` in direction `k`.
* `TauCeti.ExchangeMatrix.mutation`: mutation of an exchange matrix, keeping its symmetrizer.

## Main results

* `TauCeti.matrixMutation_matrixMutation`: mutating twice in the same direction is the
  identity. No hypothesis on the matrix is needed.
* `TauCeti.matrixMutation_submatrix`: mutation commutes with injective restriction and
  relabelling of rows and columns.
* `TauCeti.matrixMutation_fromBlocks_inl`, `TauCeti.matrixMutation_fromBlocks_inr`: mutation
  of a block diagonal matrix mutates one block and fixes the other.
* `Matrix.IsSkewSymmetrizer.matrixMutation`: a skew-symmetrizer of a square matrix is a
  skew-symmetrizer of each of its mutations.
* `TauCeti.ExchangeMatrix.mutation_mutation`: mutation of exchange matrices is an involution.
* `TauCeti.ExchangeMatrix.submatrix_mutation`, `TauCeti.ExchangeMatrix.principal_mutation`,
  `TauCeti.ExchangeMatrix.mutation_reindex`, `TauCeti.ExchangeMatrix.mutation_sum_inl`,
  `TauCeti.ExchangeMatrix.mutation_sum_inr`: the same compatibilities for exchange matrices.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  §4, for matrix mutation and its invariance properties.
* S. Fomin and A. Zelevinsky, *Cluster algebras IV: Coefficients*, Compos. Math. 143 (2007), §2,
  for the positive-part notation in the mutation formula.
* A. Berenstein, S. Fomin and A. Zelevinsky, *Cluster algebras III: Upper bounds and double
  Bruhat cells*, Duke Math. J. 126 (2005), §1, for mutation of extended matrices.
-/

public section

open Matrix

namespace TauCeti

variable {I I' K K' I₁ I₂ K₁ K₂ : Type*}

section matrixMutation

variable [DecidableEq I] [DecidableEq K] {row : K ↪ I} {B : Matrix I K ℤ} {k : K}

/-- The *mutation* in direction `k` of an integer matrix `B` whose columns are indexed by the
mutable indices `K` and whose rows are indexed by `I`, along the embedding `row : K ↪ I` of the
mutable indices: row `row k` and column `k` change sign, and every other entry `B i j` gains
`(B i k)⁺ * (B (row k) j)⁺ - (B i k)⁻ * (B (row k) j)⁻`. -/
def matrixMutation (row : K ↪ I) (B : Matrix I K ℤ) (k : K) : Matrix I K ℤ :=
  of fun i j ↦ if i = row k ∨ j = k then -B i j
    else B i j + (B i k)⁺ * (B (row k) j)⁺ - (B i k)⁻ * (B (row k) j)⁻

/-- The entries of a mutated matrix. -/
theorem matrixMutation_apply (i : I) (j : K) :
    matrixMutation row B k i j = if i = row k ∨ j = k then -B i j
      else B i j + (B i k)⁺ * (B (row k) j)⁺ - (B i k)⁻ * (B (row k) j)⁻ :=
  (rfl)

/-- Mutation in direction `k` negates the row `row k`. -/
@[simp]
theorem matrixMutation_apply_row (j : K) : matrixMutation row B k (row k) j = -B (row k) j := by
  simp [matrixMutation_apply]

/-- Mutation in direction `k` negates the column `k`. -/
@[simp]
theorem matrixMutation_apply_col (i : I) : matrixMutation row B k i k = -B i k := by
  simp [matrixMutation_apply]

/-- The entries of a mutated matrix away from the row and the column of the direction. -/
theorem matrixMutation_apply_of_ne {i : I} {j : K} (hi : i ≠ row k) (hj : j ≠ k) :
    matrixMutation row B k i j =
      B i j + (B i k)⁺ * (B (row k) j)⁺ - (B i k)⁻ * (B (row k) j)⁻ := by
  simp [matrixMutation_apply, hi, hj]

/-- Mutation in direction `k` fixes every row, other than `row k`, whose entry in column `k`
vanishes. -/
theorem matrixMutation_apply_of_apply_col_eq_zero {i : I} (hi : i ≠ row k) (h : B i k = 0)
    (j : K) : matrixMutation row B k i j = B i j := by
  obtain rfl | hj := eq_or_ne j k
  · simp [h]
  · simp [matrixMutation_apply_of_ne hi hj, h]

/-- Mutation in direction `k` fixes every column, other than `k`, whose entry in row `row k`
vanishes. -/
theorem matrixMutation_apply_of_apply_row_eq_zero {j : K} (hj : j ≠ k) (h : B (row k) j = 0)
    (i : I) : matrixMutation row B k i j = B i j := by
  obtain rfl | hi := eq_or_ne i (row k)
  · simp [h]
  · simp [matrixMutation_apply_of_ne hi hj, h]

/-- Mutating twice in the same direction gives back the original matrix. -/
@[simp]
theorem matrixMutation_matrixMutation (row : K ↪ I) (B : Matrix I K ℤ) (k : K) :
    matrixMutation row (matrixMutation row B k) k = B := by
  ext i j
  by_cases hi : i = row k
  · simp [hi]
  by_cases hj : j = k
  · simp [hj]
  simp only [matrixMutation_apply_of_ne hi hj, matrixMutation_apply_row,
    matrixMutation_apply_col, posPart_neg, negPart_neg]
  ring

/-- Mutation in a fixed direction is an involution. -/
theorem matrixMutation_involutive (row : K ↪ I) (k : K) :
    Function.Involutive fun B ↦ matrixMutation row B k :=
  fun B ↦ matrixMutation_matrixMutation row B k

/-- Mutation commutes with negation of the matrix. -/
@[simp]
theorem matrixMutation_neg (row : K ↪ I) (B : Matrix I K ℤ) (k : K) :
    matrixMutation row (-B) k = -matrixMutation row B k := by
  ext i j
  by_cases hi : i = row k
  · simp [hi]
  by_cases hj : j = k
  · simp [hj]
  simp only [matrixMutation_apply_of_ne hi hj, Matrix.neg_apply, posPart_neg, negPart_neg]
  ring

/-- Mutation commutes with injective restriction and relabelling of the rows and columns, along
maps compatible with the mutable embeddings. -/
theorem matrixMutation_submatrix [DecidableEq I'] [DecidableEq K'] {row' : K' ↪ I'}
    {f : I' → I} {g : K' → K} (hf : Function.Injective f)
    (h : ∀ k, f (row' k) = row (g k)) (B : Matrix I K ℤ) (k : K') :
    matrixMutation row' (B.submatrix f g) k = (matrixMutation row B (g k)).submatrix f g := by
  have hg : Function.Injective g := fun _ _ hk ↦
    row'.injective (hf (by rw [h, h, hk]))
  ext i j
  have hi : i = row' k ↔ f i = row (g k) := by rw [← h, hf.eq_iff]
  simp only [matrixMutation_apply, submatrix_apply, h, hi, hg.eq_iff]

/-- Mutation commutes with passage to the principal block: the principal block of the mutated
matrix is the mutation of the principal block as a square matrix. -/
theorem matrixMutation_refl_submatrix_row (row : K ↪ I) (B : Matrix I K ℤ) (k : K) :
    matrixMutation (Function.Embedding.refl K) (B.submatrix row id) k =
      (matrixMutation row B k).submatrix row id :=
  matrixMutation_submatrix row.injective (fun _ ↦ rfl) B k

end matrixMutation

section fromBlocks

variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq K₁] [DecidableEq K₂]
  (row₁ : K₁ ↪ I₁) (row₂ : K₂ ↪ I₂) (B₁ : Matrix I₁ K₁ ℤ) (B₂ : Matrix I₂ K₂ ℤ)

/-- Mutating a block diagonal matrix in a direction of the first block mutates the first block
and fixes the second. -/
@[simp]
theorem matrixMutation_fromBlocks_inl (k : K₁) :
    matrixMutation (row₁.sumMap row₂) (fromBlocks B₁ 0 0 B₂) (Sum.inl k) =
      fromBlocks (matrixMutation row₁ B₁ k) 0 0 B₂ := by
  ext (i | i) (j | j)
  · simp [matrixMutation_apply]
  · rw [matrixMutation_apply_of_apply_row_eq_zero (by simp) (by simp)]
    simp
  · rw [matrixMutation_apply_of_apply_col_eq_zero (by simp) (by simp)]
    simp
  · rw [matrixMutation_apply_of_apply_col_eq_zero (by simp) (by simp)]
    simp

/-- Mutating a block diagonal matrix in a direction of the second block mutates the second block
and fixes the first. -/
@[simp]
theorem matrixMutation_fromBlocks_inr (k : K₂) :
    matrixMutation (row₁.sumMap row₂) (fromBlocks B₁ 0 0 B₂) (Sum.inr k) =
      fromBlocks B₁ 0 0 (matrixMutation row₂ B₂ k) := by
  ext (i | i) (j | j)
  · rw [matrixMutation_apply_of_apply_col_eq_zero (by simp) (by simp)]
    simp
  · rw [matrixMutation_apply_of_apply_col_eq_zero (by simp) (by simp)]
    simp
  · rw [matrixMutation_apply_of_apply_row_eq_zero (by simp) (by simp)]
    simp
  · simp [matrixMutation_apply]

end fromBlocks

section square

variable [DecidableEq K] {B : Matrix K K ℤ} {s : K → ℤ} {k : K}

/-- Mutation of a square matrix in direction `k` negates the row `k`. This is
`TauCeti.matrixMutation_apply_row` along `Function.Embedding.refl K`, in the form `simp` can
use: there the row index is `k` itself and no longer has the shape `row k`. -/
@[simp]
theorem matrixMutation_refl_apply_row (B : Matrix K K ℤ) (k j : K) :
    matrixMutation (Function.Embedding.refl K) B k k j = -B k j :=
  matrixMutation_apply_row j

/-- The entries of a mutated square matrix away from the row and the column of the direction.
This is `TauCeti.matrixMutation_apply_of_ne` along `Function.Embedding.refl K`, stated with the
row index `k` itself. -/
theorem matrixMutation_refl_apply_of_ne {i j : K} (hi : i ≠ k) (hj : j ≠ k) :
    matrixMutation (Function.Embedding.refl K) B k i j =
      B i j + (B i k)⁺ * (B k j)⁺ - (B i k)⁻ * (B k j)⁻ :=
  matrixMutation_apply_of_ne hi hj

/-- A skew-symmetrizer of a square matrix is a skew-symmetrizer of each of its mutations. -/
protected theorem _root_.Matrix.IsSkewSymmetrizer.matrixMutation (h : B.IsSkewSymmetrizer s)
    (k : K) : (matrixMutation (Function.Embedding.refl K) B k).IsSkewSymmetrizer s where
  pos := h.pos
  mul_apply i j := by
    obtain rfl | hi := eq_or_ne i k
    · rw [matrixMutation_refl_apply_row, matrixMutation_apply_col]
      linear_combination -h.mul_apply i j
    obtain rfl | hj := eq_or_ne j k
    · rw [matrixMutation_refl_apply_row, matrixMutation_apply_col]
      linear_combination -h.mul_apply i j
    rw [matrixMutation_refl_apply_of_ne hi hj, matrixMutation_refl_apply_of_ne hj hi]
    linear_combination h.mul_apply i j + (B k j)⁺ * h.mul_posPart i k -
      (B k j)⁻ * h.mul_negPart i k + (B k i)⁻ * h.mul_posPart k j -
      (B k i)⁺ * h.mul_negPart k j

end square

/-- The matrix with rows `(0, 1)` and `(-2, 0)` is negated by mutation in its first direction. -/
example :
    matrixMutation (Function.Embedding.refl (Fin 2)) !![0, 1; -2, 0] 0 = -!![0, 1; -2, 0] := by
  decide

/-- Mutating the extended matrix with the single column `(0, 1)`, whose first row is mutable,
changes the sign of the frozen row. -/
example : matrixMutation (Fin.castSuccEmb (n := 1)) !![0; 1] 0 = !![0; -1] := by
  decide

namespace ExchangeMatrix

variable [DecidableEq I] [DecidableEq K] {row : K ↪ I} (B : ExchangeMatrix row)

/-- The *mutation* of an exchange matrix in direction `k`: the underlying matrix is mutated and
the symmetrizer is kept. -/
def mutation (k : K) : ExchangeMatrix row where
  matrix := matrixMutation row B.matrix k
  symmetrizer := B.symmetrizer
  isSkewSymmetrizer := by
    rw [← matrixMutation_refl_submatrix_row]
    exact B.isSkewSymmetrizer.matrixMutation k

@[simp]
theorem mutation_matrix (k : K) : (B.mutation k).matrix = matrixMutation row B.matrix k :=
  (rfl)

@[simp]
theorem mutation_symmetrizer (k : K) : (B.mutation k).symmetrizer = B.symmetrizer :=
  (rfl)

/-- Mutating an exchange matrix twice in the same direction gives back the original exchange
matrix. -/
@[simp]
theorem mutation_mutation (k : K) : (B.mutation k).mutation k = B := by
  ext : 1 <;> simp

/-- Mutation of exchange matrices in a fixed direction is an involution. -/
theorem mutation_involutive (k : K) :
    Function.Involutive fun B : ExchangeMatrix row ↦ B.mutation k :=
  fun B ↦ B.mutation_mutation k

/-- Mutation of exchange matrices commutes with injective restriction and relabelling of the
rows and columns. -/
theorem submatrix_mutation [DecidableEq I'] [DecidableEq K'] {row' : K' ↪ I'} {f : I' → I}
    {g : K' → K} (hf : Function.Injective f)
    (h : ∀ k, f (row' k) = row (g k)) (k : K') :
    (B.mutation (g k)).submatrix f g h = (B.submatrix f g h).mutation k := by
  ext : 1
  · simp [matrixMutation_submatrix hf h]
  · simp

/-- Mutation commutes with passage to the principal block. -/
@[simp]
theorem principal_mutation (k : K) : (B.mutation k).principal = B.principal.mutation k := by
  ext : 1 <;> simp [matrixMutation_refl_submatrix_row]

/-- Mutation of exchange matrices commutes with reindexing. -/
theorem mutation_reindex [DecidableEq I'] [DecidableEq K'] {row' : K' ↪ I'} (eI : I ≃ I')
    (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k)) (k : K) :
    (reindex eI eK h B).mutation (eK k) = reindex eI eK h (B.mutation k) := by
  have h' (k : K') : eI.symm (row' k) = row (eK.symm k) := by simp [Equiv.symm_apply_eq, h]
  ext : 1
  · simp [matrixMutation_submatrix eI.symm.injective h']
  · simp

section sum

variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq K₁] [DecidableEq K₂] {row₁ : K₁ ↪ I₁}
  {row₂ : K₂ ↪ I₂} (B₁ : ExchangeMatrix row₁) (B₂ : ExchangeMatrix row₂)

/-- Mutating a block diagonal sum in a direction of the first summand mutates the first summand
and fixes the second. -/
@[simp]
theorem mutation_sum_inl (k : K₁) : (B₁.sum B₂).mutation (Sum.inl k) = (B₁.mutation k).sum B₂ := by
  ext : 1 <;> simp

/-- Mutating a block diagonal sum in a direction of the second summand mutates the second
summand and fixes the first. -/
@[simp]
theorem mutation_sum_inr (k : K₂) : (B₁.sum B₂).mutation (Sum.inr k) = B₁.sum (B₂.mutation k) := by
  ext : 1 <;> simp

end sum

end ExchangeMatrix

end TauCeti
