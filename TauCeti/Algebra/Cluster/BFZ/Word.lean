/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic

/-!
# Successors and exchangeable positions of BFZ double words

A signed letter is the usual pair of a simple index and a Boolean sign: true is positive.
The word is preceded by the negative simple indices in reverse order. Positions are stored
in increasing order as `Fin (r + w.length)`, so the prefix represents `-r,…,-1` and the word
represents `1,…,w.length`. The successor is the least later position with the same absolute
simple index. Its value is `⊤` when there is no later occurrence, representing the terminal
index `w.length + 1` in the BFZ convention.

An exchangeable position must be in the actual word and have a genuine successor. This
combinatorics applies to arbitrary signed words; no reducedness hypothesis is needed.

## References

* A. Berenstein, S. Fomin and A. Zelevinsky, *Cluster algebras III: Upper bounds and double
  Bruhat cells*, Duke Mathematical Journal 126 (2005), §2.2, preceding Definition 2.2.
-/

public section

namespace TauCeti.BFZ

variable {r : ℕ}

/-- Read a signed word with the negative simple-index prefix `-r,…,-1`. -/
def letter (w : List (Fin r × Bool)) (k : Fin (r + w.length)) : Fin r × Bool :=
  if h : (k : ℕ) < r then ((⟨k, h⟩ : Fin r).rev, false)
  else w.get ⟨(k : ℕ) - r, by omega⟩

/-- Explicit reading rule for prefix and actual-word positions. -/
theorem letter_def (w : List (Fin r × Bool)) (k : Fin (r + w.length)) :
    letter w k = if h : (k : ℕ) < r then ((⟨k, h⟩ : Fin r).rev, false)
      else w.get ⟨(k : ℕ) - r, by omega⟩ := by rfl

/-- The prefix is the reversed list of negative simple indices. -/
@[simp]
theorem letter_castAdd (w : List (Fin r × Bool)) (k : Fin r) :
    letter w (k.castAdd w.length) = (k.rev, false) := by
  simp [letter, k.isLt]

/-- The actual word follows the prefix without changing its letters. -/
@[simp]
theorem letter_natAdd (w : List (Fin r × Bool)) (k : Fin w.length) :
    letter w (k.natAdd r) = w.get k := by
  simp [letter]

/-- Convert the ordered storage position to its nonzero signed BFZ position label. -/
def positionLabel (w : List (Fin r × Bool)) (k : Fin (r + w.length)) : ℤ :=
  if (k : ℕ) < r then (k : ℤ) - r else (k : ℤ) - r + 1

/-- Explicit conversion rule for negative prefix and positive word labels. -/
theorem positionLabel_def (w : List (Fin r × Bool)) (k : Fin (r + w.length)) :
    positionLabel w k = if (k : ℕ) < r then (k : ℤ) - r else (k : ℤ) - r + 1 := by rfl

/-- Prefix positions have exactly the negative labels `-r,…,-1`. -/
@[simp]
theorem positionLabel_castAdd (w : List (Fin r × Bool)) (k : Fin r) :
    positionLabel w (k.castAdd w.length) = (k : ℤ) - r := by
  simp [positionLabel, k.isLt]

/-- Actual word positions have their usual one-based positive labels. -/
@[simp]
theorem positionLabel_natAdd (w : List (Fin r × Bool)) (k : Fin w.length) :
    positionLabel w (k.natAdd r) = (k : ℤ) + 1 := by
  simp [positionLabel, show ¬ r + (k : ℕ) < r by omega]
  omega

/-- Actual word positions are exactly those with positive BFZ labels. -/
theorem positionLabel_pos_iff (w : List (Fin r × Bool)) (k : Fin (r + w.length)) :
    0 < positionLabel w k ↔ r ≤ (k : ℕ) := by
  unfold positionLabel
  split_ifs <;> omega

/-- The signed BFZ labels preserve the order of the storage positions, skipping zero. -/
theorem positionLabel_strictMono (w : List (Fin r × Bool)) : StrictMono (positionLabel w) := by
  intro i j hij
  unfold positionLabel
  split_ifs <;> omega

/-- No storage position denotes the omitted position zero. -/
theorem positionLabel_ne_zero (w : List (Fin r × Bool)) (k : Fin (r + w.length)) :
    positionLabel w k ≠ 0 := by
  unfold positionLabel
  split_ifs <;> omega

/-- The least later occurrence of the same absolute simple index, or the terminal sentinel. -/
def successor (w : List (Fin r × Bool)) (k : Fin (r + w.length)) :
    WithTop (Fin (r + w.length)) :=
  (Finset.univ.filter fun l ↦ k < l ∧ (letter w l).1 = (letter w k).1).min

/-- A genuine successor has the same absolute index and occurs strictly later. -/
theorem lt_and_letter_eq_of_successor_eq (w : List (Fin r × Bool))
    {k l : Fin (r + w.length)} (h : successor w k = l) :
    k < l ∧ (letter w l).1 = (letter w k).1 := by
  simpa [successor] using Finset.mem_of_min h

/-- The successor is no later than any later occurrence of its absolute index. -/
theorem successor_le (w : List (Fin r × Bool)) {k l : Fin (r + w.length)}
    (hkl : k < l) (hletter : (letter w l).1 = (letter w k).1) :
    successor w k ≤ l :=
  Finset.min_le (by simp [hkl, hletter])

/-- Exact characterization of a genuine successor, including its minimality. -/
theorem successor_eq_iff (w : List (Fin r × Bool)) (k l : Fin (r + w.length)) :
    successor w k = l ↔ k < l ∧ (letter w l).1 = (letter w k).1 ∧
      ∀ j, k < j → (letter w j).1 = (letter w k).1 → l ≤ j := by
  constructor
  · intro h
    obtain ⟨hkl, hletter⟩ := lt_and_letter_eq_of_successor_eq w h
    refine ⟨hkl, hletter, fun j hkj hj ↦ ?_⟩
    exact WithTop.coe_le_coe.mp (h ▸ successor_le w hkj hj)
  · rintro ⟨hkl, hletter, hmin⟩
    apply le_antisymm (successor_le w hkl hletter)
    apply Finset.le_min
    intro j hj
    have hj' : k < j ∧ (letter w j).1 = (letter w k).1 := by simpa using hj
    exact WithTop.coe_le_coe.mpr (hmin j hj'.1 hj'.2)

/-- No occurrence of the same absolute index lies strictly between a position and its successor. -/
theorem letter_ne_of_lt_of_lt_successor (w : List (Fin r × Bool))
    {k l j : Fin (r + w.length)} (h : successor w k = l) (hkj : k < j) (hjl : j < l) :
    (letter w j).1 ≠ (letter w k).1 := by
  intro hj
  exact (not_le_of_gt hjl) (((successor_eq_iff w k l).mp h).2.2 j hkj hj)

/-- A genuine occurrence has at most one immediate predecessor of the same absolute index. -/
theorem eq_of_successor_eq (w : List (Fin r × Bool))
    {k l j : Fin (r + w.length)} (hk : successor w k = j) (hl : successor w l = j) : k = l := by
  obtain ⟨hkj, hjk, hkmin⟩ := (successor_eq_iff w k j).mp hk
  obtain ⟨hlj, hjl, hlmin⟩ := (successor_eq_iff w l j).mp hl
  rcases lt_trichotomy k l with hkl | hkl | hlk
  · exact False.elim ((not_le_of_gt hlj) (hkmin l hkl (hjl.symm.trans hjk)))
  · exact hkl
  · exact False.elim ((not_le_of_gt hkj) (hlmin k hlk (hjk.symm.trans hjl)))

/-- Terminal successors are exactly last occurrences of an absolute simple index. -/
@[simp]
theorem successor_eq_top_iff (w : List (Fin r × Bool)) (k : Fin (r + w.length)) :
    successor w k = ⊤ ↔ ∀ l, k < l → (letter w l).1 ≠ (letter w k).1 := by
  simp only [successor, Finset.min_eq_top, Finset.filter_eq_empty_iff, Finset.mem_univ,
    true_implies, not_and]

/-- An exchangeable position belongs to the actual word and has a genuine successor. -/
def IsExchangeable (w : List (Fin r × Bool)) (k : Fin (r + w.length)) : Prop :=
  r ≤ (k : ℕ) ∧ successor w k ≠ ⊤

instance (w : List (Fin r × Bool)) (k : Fin (r + w.length)) : Decidable (IsExchangeable w k) :=
  inferInstanceAs (Decidable (r ≤ (k : ℕ) ∧ successor w k ≠ ⊤))

/-- Exchangeability means being an actual word position with a later equal absolute index. -/
theorem isExchangeable_iff (w : List (Fin r × Bool)) (k : Fin (r + w.length)) :
    IsExchangeable w k ↔ r ≤ (k : ℕ) ∧
      ∃ l, k < l ∧ (letter w l).1 = (letter w k).1 := by
  simp [IsExchangeable, successor_eq_top_iff, not_forall]

/-- Negative prefix positions are always frozen. -/
@[simp]
theorem not_isExchangeable_castAdd (w : List (Fin r × Bool)) (k : Fin r) :
    ¬ IsExchangeable w (k.castAdd w.length) := by
  intro h
  exact (Nat.not_le_of_gt k.isLt) h.1

/-- A terminal occurrence is frozen even if its signed letter is positive. -/
theorem not_isExchangeable_of_successor_eq_top (w : List (Fin r × Bool))
    {k : Fin (r + w.length)} (h : successor w k = ⊤) : ¬ IsExchangeable w k :=
  fun hk ↦ hk.2 h

/-- Finite set of the mutable BFZ seed positions. -/
def exchangeablePositions (w : List (Fin r × Bool)) : Finset (Fin (r + w.length)) :=
  Finset.univ.filter (IsExchangeable w)

@[simp]
theorem mem_exchangeablePositions (w : List (Fin r × Bool)) (k : Fin (r + w.length)) :
    k ∈ exchangeablePositions w ↔ IsExchangeable w k := by
  simp [exchangeablePositions]

/-- The identity double word has no mutable positions, in every rank. -/
@[simp]
theorem exchangeablePositions_nil : exchangeablePositions ([] : List (Fin r × Bool)) = ∅ := by
  ext k
  simp only [mem_exchangeablePositions, Finset.notMem_empty, iff_false]
  intro h
  have hk := k.isLt
  have hr := h.1
  simp only [List.length_nil, Nat.add_zero] at hk
  omega

end TauCeti.BFZ
