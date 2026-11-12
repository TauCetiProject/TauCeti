/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.IceQuiver.Basic
public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation

import Mathlib.Tactic.Ring

/-!
# Ice-quiver mutation

Mutation reverses arrows incident to a mutable vertex, adds the paths of length two through
it, cancels opposite arrows, and deletes arrows between frozen vertices. It is defined by
these arrow counts directly. Its rectangular matrix is then proved to be matrix mutation.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, §4.
-/

public section

namespace TauCeti.IceQuiver

variable {I K : Type*} {row : K ↪ I}

/-- Ice-quiver mutation at a mutable vertex: reverse incident arrows, add the paths through
that vertex, cancel two-cycles, and discard arrows between two frozen vertices. -/
noncomputable def mutation (q : IceQuiver row) (k : K) : IceQuiver row := by
  classical
  refine
    { arrows := fun i j ↦ if i ∉ Set.range row ∧ j ∉ Set.range row then 0
        else if i = row k ∨ j = row k then q.arrows j i
        else (q.arrows i j + q.arrows i (row k) * q.arrows (row k) j) -
          (q.arrows j i + q.arrows j (row k) * q.arrows (row k) i)
      noLoops := ?_
      noTwoCycles := ?_
      frozen := ?_ }
  · intro i
    simp [q.noLoops]
  · intro i j
    by_cases hf : i ∉ Set.range row ∧ j ∉ Set.range row
    · simp [hf.1, hf.2]
    · have hf' : ¬(j ∉ Set.range row ∧ i ∉ Set.range row) := by tauto
      by_cases h : i = row k ∨ j = row k
      · have h' : j = row k ∨ i = row k := h.symm
        simpa only [hf, hf', h, h', ite_false, ite_true] using q.noTwoCycles j i
      · have h' : ¬(j = row k ∨ i = row k) := by tauto
        simp only [hf, hf', h, h', ite_false]
        rcases le_total (q.arrows i j + q.arrows i (row k) * q.arrows (row k) j)
            (q.arrows j i + q.arrows j (row k) * q.arrows (row k) i) with hle | hle
        · rw [Nat.sub_eq_zero_of_le hle, zero_mul]
        · rw [Nat.sub_eq_zero_of_le hle, mul_zero]
  · intro i j hi hj
    simp [hi, hj]

/-- Mutation deletes arrows between frozen vertices. -/
theorem mutation_arrows_frozen (q : IceQuiver row) (k : K) (i j : I)
    (hi : i ∉ Set.range row) (hj : j ∉ Set.range row) :
    (q.mutation k).arrows i j = 0 :=
  (q.mutation k).frozen i j hi hj

/-- Mutation reverses each arrow beginning at the mutated vertex. -/
@[simp]
theorem mutation_arrows_row (q : IceQuiver row) (k : K) (j : I) :
    (q.mutation k).arrows (row k) j = q.arrows j (row k) := by
  classical
  have h : row k ∈ Set.range row := ⟨k, rfl⟩
  have hf : ¬(row k ∉ Set.range row ∧ j ∉ Set.range row) := fun hf ↦ hf.1 h
  simp only [mutation, hf, ite_false, eq_self, true_or, ite_true]

/-- Mutation reverses each arrow ending at the mutated vertex. -/
@[simp]
theorem mutation_arrows_col (q : IceQuiver row) (k : K) (i : I) :
    (q.mutation k).arrows i (row k) = q.arrows (row k) i := by
  classical
  have h : row k ∈ Set.range row := ⟨k, rfl⟩
  have hf : ¬(i ∉ Set.range row ∧ row k ∉ Set.range row) := fun hf ↦ hf.2 h
  simp only [mutation, hf, ite_false, eq_self, or_true, ite_true]

/-- Away from the mutated vertex, retain the excess of forward arrows over reverse arrows
after adding all paths of length two. At least one endpoint must be mutable. -/
theorem mutation_arrows_of_ne (q : IceQuiver row) (k : K) {i j : I}
    (hi : i ≠ row k) (hj : j ≠ row k)
    (hm : i ∈ Set.range row ∨ j ∈ Set.range row) :
    (q.mutation k).arrows i j =
      (q.arrows i j + q.arrows i (row k) * q.arrows (row k) j) -
        (q.arrows j i + q.arrows j (row k) * q.arrows (row k) i) := by
  classical
  have hf : ¬(i ∉ Set.range row ∧ j ∉ Set.range row) := by tauto
  simp only [mutation, hf, hi, hj, false_or, ite_false]

private theorem cast_sub_sub (a b : ℕ) :
    ((a - b : ℕ) : ℤ) - ((b - a : ℕ) : ℤ) = (a : ℤ) - b := by omega

/-- Rectangular quiver matrices intertwine direct ice-quiver mutation and integer matrix
mutation. The products in the matrix formula count paths through the mutable vertex. -/
@[simp]
theorem mutation_matrix [DecidableEq I] [DecidableEq K] (q : IceQuiver row) (k : K) :
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
    mutation_arrows_of_ne q k hr hi (Or.inl ⟨j, rfl⟩), cast_sub_sub,
    matrixMutation_apply_of_ne hi hj, matrix_posPart, matrix_posPart,
    matrix_negPart, matrix_negPart, matrix_apply]
  push_cast
  ring

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
theorem mutation_toExchangeMatrix [DecidableEq I] [DecidableEq K]
    (q : IceQuiver row) (k : K) :
    (q.mutation k).toExchangeMatrix = q.toExchangeMatrix.mutation k := by
  ext : 1
  · simp
  · funext j
    simp

/-- Relabelling quiver vertices and mutable directions intertwines mutation. -/
theorem mutation_reindex {I' K' : Type*} {row' : K' ↪ I'}
    (eI : I ≃ I') (eK : K ≃ K') (h : ∀ k, eI (row k) = row' (eK k))
    (q : IceQuiver row) (k : K) :
    (reindex eI eK h q).mutation (eK k) = reindex eI eK h (q.mutation k) := by
  classical
  apply matrix_injective
  rw [mutation_matrix, reindex_matrix, reindex_matrix, mutation_matrix]
  have h' (j : K') : eI.symm (row' j) = row (eK.symm j) := by
    simp [Equiv.symm_apply_eq, h]
  simpa using matrixMutation_submatrix eI.symm.injective eK.symm.injective h' q.matrix (eK k)

end TauCeti.IceQuiver
