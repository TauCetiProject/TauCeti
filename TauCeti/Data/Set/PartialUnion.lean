/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Lattice.Indexed

/-!
# Partial unions of sequences of sets

This file defines the union of the first `n + 1` sets in a sequence and records its elementary
membership API.
-/

public section

open Set

namespace TauCeti

variable {X : Type*}

/-- The union of the first `n + 1` members of an ordered family of sets. -/
def partialUnion (U : ℕ → Set X) : ℕ → Set X
  | 0 => U 0
  | n + 1 => partialUnion U n ∪ U (n + 1)

@[simp]
lemma mem_partialUnion {U : ℕ → Set X} {n : ℕ} {x : X} :
    x ∈ partialUnion U n ↔ ∃ i : Fin (n + 1), x ∈ U i := by
  induction n with
  | zero => simp [partialUnion]
  | succ n ih =>
    rw [partialUnion, mem_union, ih]
    constructor
    · rintro (⟨i, hi⟩ | hi)
      · exact ⟨i.castSucc, hi⟩
      · exact ⟨Fin.last (n + 1), hi⟩
    · rintro ⟨i, hi⟩
      refine Fin.lastCases (motive := fun i ↦ x ∈ U i →
        (∃ j : Fin (n + 1), x ∈ U j) ∨ x ∈ U (n + 1)) ?_ (fun j ↦ ?_) i hi
      · exact Or.inr
      · exact fun hj ↦ Or.inl ⟨j, hj⟩

/-- The first partial union is the first member of the family. -/
@[simp]
lemma partialUnion_zero (U : ℕ → Set X) : partialUnion U 0 = U 0 := by
  rfl

/-- A partial union grows by adjoining the next member. -/
@[simp]
lemma partialUnion_succ (U : ℕ → Set X) (n : ℕ) :
    partialUnion U (n + 1) = partialUnion U n ∪ U (n + 1) := by
  rfl

end TauCeti
