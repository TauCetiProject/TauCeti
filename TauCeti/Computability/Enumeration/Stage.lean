/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Fresh entries of a finite-stage enumeration

An enumeration in finite stages is a sequence `A : ℕ → Finset ℕ`. The numbers **fresh** at stage
`s` are those entering in the transition to stage `s + 1`. When the stages are monotone, a number
is fresh at most once: it has a unique entry stage.

## Main definitions

* `TauCeti.Enumeration.fresh`: the numbers entering in the transition to stage `s + 1`.

## Main results

* `TauCeti.Enumeration.unique_entry_stage`: under monotone stages a number is fresh at most once.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII.1.
-/

public section

namespace TauCeti

namespace Enumeration

/-- The numbers entering the enumeration `A` in the transition to stage `s + 1`. -/
def fresh (A : ℕ → Finset ℕ) (s : ℕ) : Finset ℕ :=
  A (s + 1) \ A s

/-- Membership in `fresh`. -/
@[simp]
theorem mem_fresh {A : ℕ → Finset ℕ} {s x : ℕ} : x ∈ fresh A s ↔ x ∈ A (s + 1) ∧ x ∉ A s :=
  Finset.mem_sdiff

/-- **Unique entry stage.** Under monotone stages a number is fresh at most once: once entered, it
stays. -/
theorem unique_entry_stage {A : ℕ → Finset ℕ} (hA : Monotone A) {s t x : ℕ}
    (hs : x ∈ fresh A s) (ht : x ∈ fresh A t) : s = t := by
  rw [mem_fresh] at hs ht
  -- an earlier entry would already put the number in the later stage
  rcases lt_trichotomy s t with h | h | h
  · exact (ht.2 (hA (Nat.succ_le_of_lt h) hs.1)).elim
  · exact h
  · exact (hs.2 (hA (Nat.succ_le_of_lt h) ht.1)).elim

end Enumeration

end TauCeti
