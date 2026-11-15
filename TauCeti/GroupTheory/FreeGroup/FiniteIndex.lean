/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.Index

/-!
# Reduced words and subgroups of finite index

Every reduced word is an initial segment of a reduced word representing an element of a given
finite index subgroup of a free group. Indeed, some positive power of the conjugate `u y u⁻¹`
lies in the subgroup, and if `u` is reduced and its last letter is neither `y` nor `y⁻¹`, then
the words `u yⁿ u⁻¹` with `n > 0` are reduced.

In the language of Stallings graphs this says that in the coset graph of a finite index
subgroup every reduced path starting at the base vertex extends to a reduced closed path. So
this coset graph is its own core, and the subgroup graph, being isomorphic to it, has an
outgoing edge with every label at every vertex.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 8, Proposition 8.3.
-/

public section

namespace FreeGroup

variable {α : Type*}

variable (H : Subgroup (FreeGroup α)) [H.FiniteIndex]

/-- If the word `u` does not end with the letter `y` and `u y ⋯ y` is reduced, then this word
is an initial segment of a reduced word `u y ⋯ y u⁻¹` in the finite index subgroup `H`. -/
private theorem exists_isReduced_append_replicate_append_mem {u : List (α × Bool)} {y : α × Bool}
    (k : ℕ) (hy : ∀ a ∈ u.getLast?, a ≠ y) (hu : IsReduced (u ++ List.replicate (k + 1) y)) :
    ∃ w, IsReduced (u ++ List.replicate (k + 1) y ++ w) ∧
      mk (u ++ List.replicate (k + 1) y ++ w) ∈ H := by
  obtain ⟨hu₀, -, hjoin⟩ : IsReduced u ∧ _ := List.isChain_append.mp hu
  obtain ⟨n, hn, -, hmem⟩ := H.exists_pow_mem_of_index_ne_zero Subgroup.FiniteIndex.index_ne_zero
    (mk u * mk [y] * (mk u)⁻¹)
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (Nat.le_mul_of_pos_left (k + 1) hn)
  have hw : u ++ List.replicate (k + 1) y ++ (List.replicate m y ++ invRev u) =
      u ++ List.replicate (n * (k + 1)) y ++ invRev u := by
    simp [hm, ← List.replicate_append_replicate]
  refine ⟨List.replicate m y ++ invRev u, ?_, ?_⟩
  · rw [hw, hm]
    refine hu₀.append_append_invRev (isReduced_replicate _ y) (by simp) ?_ ?_
    · intro a ha h
      have hrel := hjoin a ha y (by simp [List.head?_replicate])
      have h' : y = (a.1, !a.2) := by simpa [List.head?_replicate] using h
      subst h'
      simp at hrel
    · intro a ha h
      have h' : y = a := by simpa [List.getLast?_replicate] using h
      exact hy a ha h'.symm
  · rw [hw, ← mul_mk, ← mul_mk, ← inv_mk, mk_replicate, ← conj_pow, pow_mul]
    exact H.pow_mem hmem _

/-- A reduced word followed by copies of a letter `y` is an initial segment of a reduced word in
the finite index subgroup `H`, whether or not the word itself ends with `y`. -/
private theorem exists_isReduced_append_replicate_append_mem' (u : List (α × Bool)) (y : α × Bool)
    (k : ℕ) (hu : IsReduced (u ++ List.replicate (k + 1) y)) :
    ∃ w, IsReduced (u ++ List.replicate (k + 1) y ++ w) ∧
      mk (u ++ List.replicate (k + 1) y ++ w) ∈ H := by
  induction u using List.reverseRecOn generalizing k with
  | nil => exact exists_isReduced_append_replicate_append_mem H k (by simp) hu
  | append_singleton u a ih =>
    by_cases ha : a = y
    · subst ha
      have h : u ++ [a] ++ List.replicate (k + 1) a = u ++ List.replicate (k + 1 + 1) a := by
        rw [List.append_assoc, List.singleton_append, ← List.replicate_succ]
      rw [h] at hu ⊢
      exact ih (k + 1) hu
    · exact exists_isReduced_append_replicate_append_mem H k (by simpa using ha) hu

/-- Every reduced word is an initial segment of a reduced word representing an element of a
given finite index subgroup of the free group. -/
theorem IsReduced.exists_append_mem {u : List (α × Bool)} (hu : IsReduced u) :
    ∃ w, IsReduced (u ++ w) ∧ mk (u ++ w) ∈ H := by
  rcases List.eq_nil_or_concat u with rfl | ⟨u, y, rfl⟩
  · exact ⟨[], by simp, by simp [← one_eq_mk]⟩
  · rw [List.concat_eq_append] at hu ⊢
    exact exists_isReduced_append_replicate_append_mem' H u y 0 hu

end FreeGroup
