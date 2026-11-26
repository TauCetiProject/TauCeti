/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Word.Basic
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite support windows for mutation words

For any set of mutable directions, mutations in those directions preserve exactly the union
of the supports of their columns. If finitely many directions are considered and their initial
columns have finite support, one finite row set therefore suffices for every word in those
directions. The row set may also include all selected mutable rows, allowing finite-rank
restriction with the existing mutation-word transport API.

The ambient mutable and row types may both be infinite. These results concern every row,
including mutable rows, rather than just the frozen part of a standard presentation. They need
no skew-symmetrizability assumption. Equality of the selected columns can be tested in any row
window containing their initial support, so the test is independent of finite enlargement.
-/

public section

namespace TauCeti

variable {I K : Type*} [DecidableEq I] [DecidableEq K]

private theorem biUnion_support_matrixMutationWord_subset (row : K ↪ I) (B : Matrix I K ℤ)
    (s : Set K) (w : List K) (hw : ∀ k ∈ w, k ∈ s) :
    (⋃ k ∈ s, Function.support ((matrixMutationWord row B w).col k)) ⊆
      ⋃ k ∈ s, Function.support (B.col k) := by
  induction w generalizing B with
  | nil => simp
  | cons k w ih =>
    rw [matrixMutationWord_cons]
    refine (ih (matrixMutation row B k) (fun l hl ↦ hw l (List.mem_cons_of_mem k hl))).trans ?_
    intro i hi
    simp only [Set.mem_iUnion] at hi ⊢
    obtain ⟨l, hl, hil⟩ := hi
    rcases support_matrixMutation_subset row B k l hil with hil | hik
    · exact ⟨l, hl, hil⟩
    · exact ⟨k, hw k (by simp), hik⟩

/-- Mutations in a set of directions preserve exactly the union of the supports of those
columns. The selected set itself need not be finite. -/
@[simp]
theorem biUnion_support_matrixMutationWord (row : K ↪ I) (B : Matrix I K ℤ)
    (s : Set K) (w : List K) (hw : ∀ k ∈ w, k ∈ s) :
    (⋃ k ∈ s, Function.support ((matrixMutationWord row B w).col k)) =
      ⋃ k ∈ s, Function.support (B.col k) := by
  apply Set.Subset.antisymm (biUnion_support_matrixMutationWord_subset row B s w hw)
  have h := biUnion_support_matrixMutationWord_subset row (matrixMutationWord row B w)
    s w.reverse (fun k hk ↦ hw k (List.mem_reverse.mp hk))
  simpa only [matrixMutationWord_matrixMutationWord_reverse] using h

/-- Finitely many initially finite columns admit one finite row window for every mutation
word using those directions. The window contains the selected mutable rows as well. -/
theorem exists_finite_row_window (row : K ↪ I) (B : Matrix I K ℤ) (s : Set K)
    (hs : s.Finite) (hB : ∀ k ∈ s, (Function.support (B.col k)).Finite) :
    ∃ t : Set I, t.Finite ∧ row '' s ⊆ t ∧
      ∀ w : List K, (∀ k ∈ w, k ∈ s) →
        (⋃ k ∈ s, Function.support ((matrixMutationWord row B w).col k)) ⊆ t := by
  refine ⟨row '' s ∪ ⋃ k ∈ s, Function.support (B.col k),
    (hs.image row).union (hs.biUnion hB), Set.subset_union_left, ?_⟩
  intro w hw
  rw [biUnion_support_matrixMutationWord row B s w hw]
  exact Set.subset_union_right

/-- Columnwise finite support is preserved and reflected by every finite mutation word,
even with infinitely many mutable directions and rows. -/
@[simp]
theorem finite_column_support_matrixMutationWord_iff (row : K ↪ I) (B : Matrix I K ℤ)
    (w : List K) :
    (∀ k, (Function.support ((matrixMutationWord row B w).col k)).Finite) ↔
      ∀ k, (Function.support (B.col k)).Finite := by
  have preserve (C : Matrix I K ℤ) (v : List K)
      (hC : ∀ k, (Function.support (C.col k)).Finite) :
      ∀ k, (Function.support ((matrixMutationWord row C v).col k)).Finite := by
    induction v generalizing C with
    | nil => simpa only [matrixMutationWord_nil] using hC
    | cons k v ih =>
      simpa only [matrixMutationWord_cons] using
        ih (matrixMutation row C k) (fun l ↦
          ((hC l).union (hC k)).subset (support_matrixMutation_subset row C k l))
  constructor
  · intro h
    simpa only [matrixMutationWord_matrixMutationWord_reverse] using
      preserve (matrixMutationWord row B w) w.reverse h
  · exact preserve B w

/-- Restriction to any row set containing the initial support detects equality of the selected
columns after two words in those directions. No finite or minimal-window hypothesis is needed. -/
theorem matrixMutationWord_submatrix_eq_iff (row : K ↪ I) (B : Matrix I K ℤ)
    (s : Set K) (t : Set I)
    (hB : (⋃ k ∈ s, Function.support (B.col k)) ⊆ t)
    (u v : List K) (hu : ∀ k ∈ u, k ∈ s) (hv : ∀ k ∈ v, k ∈ s) :
    (matrixMutationWord row B u).submatrix (Subtype.val : t → I) (Subtype.val : s → K) =
        (matrixMutationWord row B v).submatrix Subtype.val Subtype.val ↔
      (matrixMutationWord row B u).submatrix id (Subtype.val : s → K) =
        (matrixMutationWord row B v).submatrix id Subtype.val := by
  have hz (w : List K) (hw : ∀ k ∈ w, k ∈ s) (i : I) (hi : i ∉ t) (k : s) :
      matrixMutationWord row B w i k = 0 := by
    by_contra hne
    have hmem : i ∈ ⋃ l ∈ s, Function.support ((matrixMutationWord row B w).col l) :=
      Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨k.property, hne⟩⟩
    rw [biUnion_support_matrixMutationWord row B s w hw] at hmem
    exact hi (hB hmem)
  constructor
  · intro h
    ext i k
    by_cases hi : i ∈ t
    · simpa only [Matrix.submatrix_apply, id_eq] using congrFun (congrFun h ⟨i, hi⟩) k
    · simp only [Matrix.submatrix_apply, id_eq, hz u hu i hi k, hz v hv i hi k]
  · intro h
    ext i k
    simpa only [Matrix.submatrix_apply, id_eq] using congrFun (congrFun h i.val) k

end TauCeti
