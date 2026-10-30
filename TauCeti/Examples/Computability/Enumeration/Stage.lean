/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.Enumeration.Stage
import Mathlib.Algebra.Group.Nat.Even

/-!
# Regression examples: limits of finite-stage enumerations

These examples exercise the limit API from a downstream module, through public statements only:

* two enumerations of the same set with different entry times: the enumeration of all numbers in
  order and its paused copy, which enters each number at twice the stage, have the same limit;
* without monotone stages, reindexing by a clock with cofinal range can change the limit: a
  number that leaves and re-enters is missed by the clock that only reads the stages where it is
  absent;
* a number already present at the first stage is in the limit but never fresh, so the entry-stage
  lemma needs its hypothesis.
-/

open TauCeti.Enumeration

-- The paused enumeration, read along the clock `s ↦ s / 2`, has the same limit.
example : stageLimit (fun s => Finset.range (s / 2)) = stageLimit Finset.range :=
  stageLimit_comp_of_cofinal (A := Finset.range) (c := (· / 2))
    (fun _ _ h => Finset.range_subset_range.2 h) fun s => ⟨2 * s, by omega⟩

-- Without monotonicity, the clock `s ↦ 2 * s`, whose range is cofinal, misses a number that is
-- present only at odd stages.
example :
    stageLimit ((fun s => if Even s then ∅ else {0}) ∘ (2 * ·)) = ∅ ∧
      stageLimit (fun s => if Even s then ∅ else {0}) = {0} := by
  constructor
  · ext x
    simp only [mem_stageLimit, Function.comp_apply, Set.mem_empty_iff_false, iff_false, not_exists]
    intro t
    rw [ite_eq_left ⟨t, Nat.two_mul t⟩]
    simp
  · ext x
    simp only [mem_stageLimit, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, hs⟩
      split_ifs at hs <;> simp_all
    · rintro rfl
      exact ⟨1, by simp⟩

-- A number present from the first stage on is in the limit but never fresh.
example : (0 ∈ stageLimit fun _ => {0}) ∧ ∀ s, 0 ∉ fresh (fun _ => ({0} : Finset ℕ)) s :=
  ⟨mem_stageLimit.2 ⟨0, by simp⟩, fun s => by simp⟩
