/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Data.Int.Interval

/-!
# Inclusive integer interval length and right shortening

For `NonemptyInterval ℤ`, `intLength` counts integer points, unlike the existing
`length`, which measures the difference of endpoints. `shorten` removes the rightmost
point and returns `none` on a singleton. These operations give the size and deletion
conventions for interval blocks of integer-graded nilpotent operators.

Translation uses the existing interval addition `s + pure c`; no separate shift operation
is needed. Shortening commutes with this translation, and preserves and reflects inclusion
among surviving intervals.

The conventions follow Atobe–Kondo–Yasuda, *Local newforms for the general linear groups
over a non-archimedean local field*, §2.1 and §3.1 (arXiv:2110.09070v4).
-/

public section

namespace NonemptyInterval

/-- The number of integer points in a nonempty closed integer interval. -/
def intLength (s : NonemptyInterval ℤ) : ℕ :=
  (s.snd - s.fst + 1).toNat

/-- The inclusive integer length agrees with the cardinality of the finite interval. -/
theorem intLength_eq_card (s : NonemptyInterval ℤ) :
    s.intLength = (Finset.Icc s.fst s.snd).card := by
  simp only [intLength, Int.card_Icc]
  congr 1; omega

/-- Casting the inclusive length to integers recovers the endpoint formula. -/
@[simp] theorem intLength_cast (s : NonemptyInterval ℤ) :
    (s.intLength : ℤ) = s.snd - s.fst + 1 := by
  have := s.fst_le_snd
  simp only [intLength, Int.toNat_of_nonneg (by omega : 0 ≤ s.snd - s.fst + 1)]

/-- Nonempty integer intervals have positive inclusive length. -/
theorem intLength_pos (s : NonemptyInterval ℤ) : 0 < s.intLength := by
  have := s.fst_le_snd
  have := s.intLength_cast
  omega

@[simp] theorem intLength_pure (a : ℤ) : (pure a).intLength = 1 := by
  simp [intLength]

/-- An interval has inclusive length one exactly when its endpoints agree. -/
@[simp] theorem intLength_eq_one_iff (s : NonemptyInterval ℤ) :
    s.intLength = 1 ↔ s.fst = s.snd := by
  have := s.intLength_cast
  omega

/-- Translation preserves the number of integer points. -/
@[simp] theorem intLength_add_pure (s : NonemptyInterval ℤ) (c : ℤ) :
    (s + pure c).intLength = s.intLength := by
  simp only [intLength, fst_add, snd_add, pure_fst, pure_snd]
  congr 1; omega

/-- Delete the rightmost point of an integer interval, deleting singleton intervals entirely. -/
def shorten (s : NonemptyInterval ℤ) : Option (NonemptyInterval ℤ) :=
  if h : s.fst < s.snd then some ⟨(s.fst, s.snd - 1), by omega⟩ else none

/-- Shortening deletes precisely singleton intervals. -/
@[simp] theorem shorten_eq_none_iff (s : NonemptyInterval ℤ) :
    s.shorten = none ↔ s.fst = s.snd := by
  have := s.fst_le_snd
  simp only [shorten]
  split_ifs <;> simp_all <;> omega

@[simp] theorem shorten_pure (a : ℤ) : (pure a).shorten = none := by
  simp

/-- A surviving shortened interval keeps the left endpoint and lowers the right by one. -/
@[simp] theorem shorten_eq_some_iff (s t : NonemptyInterval ℤ) :
    s.shorten = some t ↔ t.fst = s.fst ∧ t.snd = s.snd - 1 := by
  have ht := t.fst_le_snd
  simp only [shorten]
  split_ifs with h
  · simp only [Option.some.injEq, NonemptyInterval.ext_iff, Prod.ext_iff]
    simp only [eq_comm]
  · simp only [false_iff, not_and]
    omega

/-- Membership in a surviving shortening is the half-open endpoint condition. -/
theorem mem_iff_of_shorten_eq_some {s t : NonemptyInterval ℤ} (h : s.shorten = some t)
    (a : ℤ) : a ∈ t ↔ s.fst ≤ a ∧ a < s.snd := by
  obtain ⟨hl, hr⟩ := (shorten_eq_some_iff s t).1 h
  rw [mem_def, hl, hr]
  omega

/-- Even when shortening deletes an interval, its optional membership has the same condition. -/
theorem exists_mem_shorten_iff (s : NonemptyInterval ℤ) (a : ℤ) :
    (∃ t ∈ s.shorten, a ∈ t) ↔ s.fst ≤ a ∧ a < s.snd := by
  simp only [shorten]
  split_ifs with h
  · simp only [Option.mem_some_iff, exists_eq_left', mem_mk]
    omega
  · simp only [Option.not_mem_none, false_and, exists_false, false_iff, not_and]
    omega

/-- A surviving shortening loses exactly one integer point. -/
theorem intLength_of_shorten_eq_some {s t : NonemptyInterval ℤ}
    (h : s.shorten = some t) : t.intLength + 1 = s.intLength := by
  obtain ⟨hl, hr⟩ := (shorten_eq_some_iff s t).1 h
  have := s.intLength_cast
  have := t.intLength_cast
  omega

/-- Counting a deleted interval as zero, shortening always loses exactly one point. -/
theorem intLength_shorten (s : NonemptyInterval ℤ) :
    (s.shorten.map intLength).getD 0 + 1 = s.intLength := by
  cases h : s.shorten with
  | none =>
    have := (shorten_eq_none_iff s).1 h
    simpa using ((intLength_eq_one_iff s).2 this).symm
  | some t =>
    simpa using intLength_of_shorten_eq_some h

/-- Every surviving shortening is contained in its original interval. -/
theorem le_of_shorten_eq_some {s t : NonemptyInterval ℤ} (h : s.shorten = some t) :
    t ≤ s := by
  obtain ⟨hl, hr⟩ := (shorten_eq_some_iff s t).1 h
  simp only [le_def, hl, hr]
  omega

/-- Shortening preserves and reflects inclusion between intervals that survive. -/
theorem shorten_le_shorten_iff {s t s' t' : NonemptyInterval ℤ}
    (hs : s.shorten = some s') (ht : t.shorten = some t') : s' ≤ t' ↔ s ≤ t := by
  obtain ⟨hsl, hsr⟩ := (shorten_eq_some_iff s s').1 hs
  obtain ⟨htl, htr⟩ := (shorten_eq_some_iff t t').1 ht
  simp only [le_def, hsl, hsr, htl, htr]
  omega

/-- Shortening commutes with every integer translation, including singleton deletion. -/
@[simp] theorem shorten_add_pure (s : NonemptyInterval ℤ) (c : ℤ) :
    (s + pure c).shorten = s.shorten.map (· + pure c) := by
  simp only [shorten, fst_add, snd_add, pure_fst, pure_snd, add_lt_add_iff_right]
  split_ifs with h
  · simp only [Option.map_some, Option.some.injEq]
    apply NonemptyInterval.ext
    apply Prod.ext
    · rfl
    · dsimp [pure]
      omega
  · rfl

end NonemptyInterval
