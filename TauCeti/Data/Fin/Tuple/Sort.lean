/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Fin

/-!
# Sorted tuples are determined by their fibre cardinalities

A monotone tuple `f : Fin n → α` is the sorted arrangement of its values, so it is determined by
how often each value occurs. Two monotone tuples in which every value `a` occurs equally often,
`#{i | f i = a} = #{i | g i = a}`, are therefore equal; the same holds for antitone tuples.

## Main results

* `Monotone.eq_of_card_filter_eq`: two monotone tuples with the same fibre cardinalities are equal.
* `Antitone.eq_of_card_filter_eq`: two antitone tuples with the same fibre cardinalities are equal.
-/

public section

open Finset

variable {n : ℕ} {α : Type*} [PartialOrder α] [DecidableEq α] {f g : Fin n → α}

/-- Two monotone tuples in which every value occurs equally often are equal. -/
theorem Monotone.eq_of_card_filter_eq (hf : Monotone f) (hg : Monotone g)
    (h : ∀ a, #{i | f i = a} = #{i | g i = a}) : f = g := by
  refine List.ofFn_injective ((List.perm_iff_count.2 fun a ↦ ?_).eq_of_sortedLE
    hf.sortedLE_ofFn hg.sortedLE_ofFn)
  have hcount (u : Fin n → α) : #{i | u i = a} = (List.ofFn u).count a := by
    simpa using Fin.card_filter_univ_eq_vector_get_eq_count a (List.Vector.ofFn u)
  rw [← hcount, ← hcount, h]

/-- Two antitone tuples in which every value occurs equally often are equal. -/
theorem Antitone.eq_of_card_filter_eq (hf : Antitone f) (hg : Antitone g)
    (h : ∀ a, #{i | f i = a} = #{i | g i = a}) : f = g :=
  Monotone.eq_of_card_filter_eq (α := αᵒᵈ) hf hg h
