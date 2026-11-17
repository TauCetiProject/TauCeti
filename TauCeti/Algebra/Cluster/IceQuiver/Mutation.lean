/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.IceQuiver.Basic
public import TauCeti.Data.Int.Cast.Basic
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation

import Mathlib.Tactic.Ring

/-!
# Ice-quiver mutation

Mutation first adds arrows for the paths of length two through the original mutable vertex,
then reverses incident arrows, cancels opposite arrows, and deletes arrows between frozen
vertices. It is defined by these arrow counts directly. Its rectangular matrix is then proved
to be matrix mutation.

## References

* S. Fomin, L. Williams and A. Zelevinsky, *Introduction to Cluster Algebras. Chapters 1–3*,
  [arXiv:1608.05735](https://arxiv.org/abs/1608.05735), Definition 2.1.2 and Lemma 2.7.3.
-/

public section

namespace TauCeti.IceQuiver

variable {I K : Type*} {row : K ↪ I}

/-- Ice-quiver mutation adds arrows for paths of length two in the original quiver through
the mutable vertex, reverses incident arrows, cancels two-cycles, and discards arrows between
two frozen vertices. -/
noncomputable def mutation (q : IceQuiver row) (k : K) : IceQuiver row := by
  classical
  refine
    { arrows := fun i j ↦ if i ∉ Set.range row ∧ j ∉ Set.range row then 0
        else if i = row k ∨ j = row k then q.arrows j i
        else (q.arrows i j + q.arrows i (row k) * q.arrows (row k) j) -
          (q.arrows j i + q.arrows j (row k) * q.arrows (row k) i)
      arrows_self := ?_
      arrows_mul_arrows_eq_zero := ?_
      arrows_eq_zero_of_notMem_range := ?_ }
  · intro i
    simp
  · intro i j
    by_cases hf : i ∉ Set.range row ∧ j ∉ Set.range row
    · simp [hf.1, hf.2]
    · have hf' : ¬(j ∉ Set.range row ∧ i ∉ Set.range row) := by tauto
      by_cases h : i = row k ∨ j = row k
      · have h' : j = row k ∨ i = row k := h.symm
        simpa only [hf, hf', h, h', ite_false, ite_true] using q.arrows_mul_arrows_eq_zero j i
      · have h' : ¬(j = row k ∨ i = row k) := by tauto
        simp only [hf, hf', h, h', ite_false]
        rcases le_total (q.arrows i j + q.arrows i (row k) * q.arrows (row k) j)
            (q.arrows j i + q.arrows j (row k) * q.arrows (row k) i) with hle | hle
        · rw [Nat.sub_eq_zero_of_le hle, zero_mul]
        · rw [Nat.sub_eq_zero_of_le hle, mul_zero]
  · intro i j hi hj
    simp [hi, hj]

/-- Arrows beginning at the mutated vertex after mutation are the arrows ending at it before
mutation. -/
@[simp]
theorem mutation_arrows_row (q : IceQuiver row) (k : K) (j : I) :
    (q.mutation k).arrows (row k) j = q.arrows j (row k) := by
  classical
  have h : row k ∈ Set.range row := ⟨k, rfl⟩
  have hf : ¬(row k ∉ Set.range row ∧ j ∉ Set.range row) := fun hf ↦ hf.1 h
  simp only [mutation, hf, ite_false, eq_self, true_or, ite_true]

/-- Arrows ending at the mutated vertex after mutation are the arrows beginning at it before
mutation. -/
@[simp]
theorem mutation_arrows_col (q : IceQuiver row) (k : K) (i : I) :
    (q.mutation k).arrows i (row k) = q.arrows (row k) i := by
  classical
  have h : row k ∈ Set.range row := ⟨k, rfl⟩
  have hf : ¬(i ∉ Set.range row ∧ row k ∉ Set.range row) := fun hf ↦ hf.2 h
  simp only [mutation, hf, ite_false, eq_self, or_true, ite_true]

/-- The incident-row formula for an unfrozen quiver. -/
@[simp]
theorem mutation_refl_arrows_row (q : IceQuiver (Function.Embedding.refl K)) (k j : K) :
    (q.mutation k).arrows k j = q.arrows j k := q.mutation_arrows_row k j

/-- The incident-column formula for an unfrozen quiver. -/
@[simp]
theorem mutation_refl_arrows_col (q : IceQuiver (Function.Embedding.refl K)) (k i : K) :
    (q.mutation k).arrows i k = q.arrows k i := q.mutation_arrows_col k i

/-- Away from the mutated vertex, retain the excess of forward arrows over reverse arrows
after adding all paths of length two through the mutated vertex. At least one endpoint must be
mutable. -/
theorem mutation_arrows_of_ne (q : IceQuiver row) (k : K) {i j : I}
    (hi : i ≠ row k) (hj : j ≠ row k)
    (hm : i ∈ Set.range row ∨ j ∈ Set.range row) :
    (q.mutation k).arrows i j =
      (q.arrows i j + q.arrows i (row k) * q.arrows (row k) j) -
        (q.arrows j i + q.arrows j (row k) * q.arrows (row k) i) := by
  classical
  have hf : ¬(i ∉ Set.range row ∧ j ∉ Set.range row) := by tauto
  simp only [mutation, hf, hi, hj, false_or, ite_false]

/-- Away from the mutated vertex of an unfrozen quiver, add paths of length two through that
vertex and cancel opposite arrows. -/
theorem mutation_refl_arrows_of_ne (q : IceQuiver (Function.Embedding.refl K)) (k : K)
    {i j : K} (hi : i ≠ k) (hj : j ≠ k) :
    (q.mutation k).arrows i j =
      (q.arrows i j + q.arrows i k * q.arrows k j) -
        (q.arrows j i + q.arrows j k * q.arrows k i) :=
  q.mutation_arrows_of_ne k hi hj (Or.inl ⟨i, rfl⟩)

/-- Rectangular quiver matrices intertwine direct ice-quiver mutation and integer matrix
mutation. The products in the matrix formula count paths of length two through the mutated
vertex. -/
@[simp]
theorem matrix_mutation [DecidableEq I] [DecidableEq K] (q : IceQuiver row) (k : K) :
    (q.mutation k).matrix = matrixMutation row q.matrix k := by
  ext i j
  by_cases hi : i = row k
  · subst i
    simp only [matrix_apply, mutation_arrows_row, mutation_arrows_col,
      matrixMutation_apply_row]
    omega
  by_cases hj : j = k
  · subst j
    simp only [matrix_apply, mutation_arrows_row, mutation_arrows_col,
      matrixMutation_apply_col]
    omega
  have hr : row j ≠ row k := fun h ↦ hj (row.injective h)
  rw [matrix_apply, mutation_arrows_of_ne q k hi hr (Or.inr ⟨j, rfl⟩),
    mutation_arrows_of_ne q k hr hi (Or.inl ⟨j, rfl⟩), Nat.cast_sub_sub_cast_sub,
    matrixMutation_apply_of_ne hi hj, posPart_matrix, posPart_matrix,
    negPart_matrix, negPart_matrix, matrix_apply]
  push_cast
  ring

/-- The forward matrix bijection intertwines quiver mutation and raw matrix mutation. -/
theorem matrixEquiv_mutation [DecidableEq I] [DecidableEq K] (q : IceQuiver row) (k : K) :
    matrixEquiv (q.mutation k) =
      ⟨matrixMutation row q.matrix k, matrixMutation_skew q.matrix_skew k⟩ := by
  apply Subtype.ext
  simpa only [val_matrixEquiv_apply] using q.matrix_mutation k

/-- Reconstructing the mutated raw matrix gives the directly mutated quiver. -/
theorem mutation_ofMatrix [DecidableEq I] [DecidableEq K] (B : Matrix I K ℤ)
    (hB : ∀ i j, B (row i) j = -B (row j) i) (k : K) :
    (ofMatrix B hB).mutation k =
      ofMatrix (matrixMutation row B k) (matrixMutation_skew hB k) := by
  apply matrix_injective
  simp

/-- The inverse matrix bijection intertwines raw matrix mutation and quiver mutation. -/
theorem mutation_matrixEquiv_symm [DecidableEq I] [DecidableEq K]
    (B : {B : Matrix I K ℤ // ∀ i j, B (row i) j = -B (row j) i}) (k : K) :
    (matrixEquiv.symm B).mutation k =
      matrixEquiv.symm ⟨matrixMutation row B.val k, matrixMutation_skew B.property k⟩ := by
  simpa only [matrixEquiv_symm_apply] using mutation_ofMatrix B.val B.property k

/-- Quiver mutation is involutive, including the frozen-vertex deletion convention. -/
@[simp]
theorem mutation_mutation (q : IceQuiver row) (k : K) :
    (q.mutation k).mutation k = q := by
  classical
  apply matrix_injective
  simp

/-- Mutation in any fixed mutable direction is an involution. -/
theorem mutation_involutive (k : K) : Function.Involutive (fun q : IceQuiver row ↦ q.mutation k) :=
  fun q ↦ q.mutation_mutation k

/-- The canonical symmetrizer-one exchange matrix commutes with quiver mutation. -/
@[simp]
theorem toExchangeMatrix_mutation [DecidableEq I] [DecidableEq K]
    (q : IceQuiver row) (k : K) :
    (q.mutation k).toExchangeMatrix = q.toExchangeMatrix.mutation k := by
  ext : 1
  · simp
  · simp

/-- Relabelling quiver vertices and mutable directions intertwines mutation. -/
theorem mutation_reindex {I' K' : Type*} {row' : K' ↪ I'}
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (q : IceQuiver row) (k : K) :
    (reindex eI eK h q).mutation (eK k) = reindex eI eK h (q.mutation k) := by
  classical
  apply toExchangeMatrix_injective
  simpa only [toExchangeMatrix_mutation, toExchangeMatrix_reindex] using
    q.toExchangeMatrix.mutation_reindex eI eK h k

end TauCeti.IceQuiver
