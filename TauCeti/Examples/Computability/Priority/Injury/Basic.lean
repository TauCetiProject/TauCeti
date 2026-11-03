/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.Priority.Injury.Causes

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
  strictly below it;
* contribution budgets apply to batched entries, including the sharp one-entry-per-contributor
  bound and contributors supplying two distinct numbers each.
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

-- A batch with one distinct number from each higher priority attains the budget `e`, even
-- though all numbers enter at the same stage. This also covers `e = 0`.
example (e : ℕ) :
    (injurySet (fun s => if s = 0 then ∅ else Finset.range e)
      (fun _ _ => some e) e).Finite ∧
    (injurySet (fun s => if s = 0 then ∅ else Finset.range e)
      (fun _ _ => some e) e).ncard ≤ e := by
  apply finite_injurySet_and_ncard_le_of_subsingleton_causes (fun i => {i})
  · intro i _
    exact Set.subsingleton_singleton
  · intro s x hx
    obtain ⟨hx, _, _⟩ := mem_injuriesAt.mp hx
    have hxe : x < e := by simpa using hx
    exact ⟨x, hxe, rfl⟩

example (e : ℕ) :
    (injurySet (fun s => if s = 0 then ∅ else Finset.range e)
      (fun _ _ => some e) e).ncard = e := by
  have hset : injurySet (fun s => if s = 0 then ∅ else Finset.range e)
      (fun _ _ => some e) e = (Finset.range e : Set ℕ) := by
    ext x
    constructor
    · rintro hx
      obtain ⟨s, hs⟩ := mem_injurySet.mp hx
      have hx := (mem_injuriesAt.mp hs).1
      simpa using hx
    · intro hx
      apply mem_injurySet.mpr
      refine ⟨0, mem_injuriesAt.mpr ?_⟩
      simp only [Finset.mem_coe, Finset.mem_range] at hx
      simp [hx, Nat.le_of_lt hx]
  simp only [hset, Set.ncard_coe_finset, Finset.card_range]

-- Each contributor supplies two numbers. The budget counts distinct entries and needs no
-- one-entry-per-stage assumption.
example (e : ℕ) :
    (injurySet (fun s => if s = 0 then ∅ else Finset.range (2 * e))
      (fun _ _ => some (2 * e)) e).Finite ∧
    (injurySet (fun s => if s = 0 then ∅ else Finset.range (2 * e))
      (fun _ _ => some (2 * e)) e).ncard ≤ 2 * e := by
  have hbudget (i : ℕ) (_ : i < e) :
      ({2 * i, 2 * i + 1} : Set ℕ).Finite ∧
        ({2 * i, 2 * i + 1} : Set ℕ).ncard ≤ 2 := by
    refine ⟨Set.toFinite _, ?_⟩
    exact (Set.ncard_pair (by omega)).le
  have hcover s x (hx : x ∈ injuriesAt
      (fun s => if s = 0 then ∅ else Finset.range (2 * e))
      (fun _ _ => some (2 * e)) e s) :
      ∃ i < e, x ∈ ({2 * i, 2 * i + 1} : Set ℕ) := by
    have hxe : x < 2 * e := by simpa using (mem_injuriesAt.mp hx).1
    refine ⟨x / 2, by omega, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  simpa [Nat.mul_comm] using
    finite_injurySet_and_ncard_le_sum_of_causes _ (fun _ => 2) hbudget hcover
