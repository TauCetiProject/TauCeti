/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.Priority.Injury

/-!
# Regression examples: injury bookkeeping

These examples exercise the injury objects from a downstream module, through public statements
only:

* no restraint against restraint `0`: a fresh entry `0` injures nothing under `none`, but injures
  under `some 0`;
* two numbers injuring at one stage give two injuring numbers but one injury stage, so the
  cardinal inequality is strict;
* without monotone stages, a single number can leave and re-enter, injuring at infinitely many
  stages: finitely many injuring numbers do not bound the injury stages;
* the restraint is inclusive: an entry exactly at the restraint injures, although it does not lie
  strictly below it.
-/

open TauCeti.Priority

-- With no restraint, the entry of `0` at the first transition injures nothing ...
example :
    injuriesAt (fun s => if s = 0 then ∅ else {0}) (fun _ _ => none) 0 0 = ∅ :=
  injuriesAt_eq_empty_of_eq_none rfl

-- ... but under the restraint `some 0` it is an injury.
example : 0 ∈ injuriesAt (fun s => if s = 0 then ∅ else {0}) (fun _ _ => some 0) 0 0 := by
  simp

-- Two numbers entering together below the restraint: two injuring numbers, one injury stage.
example :
    injurySet (fun s => if s = 0 then ∅ else {0, 1}) (fun _ _ => some 1) 0 = {0, 1} ∧
      injuryStages (fun s => if s = 0 then ∅ else {0, 1}) (fun _ _ => some 1) 0 = {1} := by
  constructor
  · ext x
    simp only [mem_injurySet, mem_injuriesAt]
    constructor
    · rintro ⟨s, hx, hx', -⟩
      rcases s with - | s <;> simp_all
    · intro hx
      refine ⟨0, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> simp
  · ext t
    rw [mem_injuryStages]
    constructor
    · rintro ⟨s, rfl, x, hx⟩
      rcases s with - | s
      · rfl
      · simp at hx
        omega
    · rintro rfl
      exact ⟨0, rfl, 0, by simp⟩

-- Without monotone stages, `0` leaves and re-enters forever: one injuring number, infinitely many
-- injury stages.
example :
    injurySet (fun s => if Even s then ∅ else {0}) (fun _ _ => some 0) 0 = {0} ∧
      (injuryStages (fun s => if Even s then ∅ else {0}) (fun _ _ => some 0) 0).Infinite := by
  constructor
  · ext x
    simp only [mem_injurySet, mem_injuriesAt, Set.mem_singleton_iff]
    constructor
    · rintro ⟨s, -, -, b, hb, hxb⟩
      simp only [Option.some.injEq] at hb
      omega
    · rintro rfl
      exact ⟨0, by simp⟩
  · refine Set.infinite_of_injective_forall_mem (f := fun s : ℕ => 2 * s + 1)
      (fun a b h => by simpa using h) fun s => succ_mem_injuryStages.2 ⟨0, ?_⟩
    simp [parity_simps]

-- The restraint is inclusive: an entry exactly at the restraint injures, although it does not lie
-- strictly below it.
example : 5 ∈ injuriesAt (fun s => if s = 0 then ∅ else {5}) (fun _ _ => some 5) 0 0 ∧
    ¬ (5 < 5) := by
  simp
