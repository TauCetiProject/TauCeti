/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Basic
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Interlacing and counts above thresholds

For sorted integer rows of lengths `n + 1` and `n`, interlacing is equivalent to saying
that the longer row has either the same number of entries above any threshold or one more.
This characterizes interlacing without choosing a numbering of the entries in advance.
-/

public section

open Finset

namespace TauCeti

/-- Two weakly decreasing rows interlace if and only if the longer row has zero or one
more entry above each threshold. Ties within or between the rows are allowed. -/
theorem interlaces_iff_card_filter {n : ℕ} {l : Fin (n + 1) → ℤ} {m : Fin n → ℤ}
    (hl : Antitone l) (hm : Antitone m) :
    Interlaces l m ↔
      ∀ x : ℤ, #{i | x < m i} ≤ #{i | x < l i} ∧ #{i | x < l i} ≤ #{i | x < m i} + 1 := by
  have longer (x : ℤ) (i : Fin (n + 1)) : (i : ℕ) < #{j | x < l j} ↔ x < l i :=
    Tuple.lt_card_gt_iff_apply_gt_of_antitone hl
  have shorter (x : ℤ) (i : Fin n) : (i : ℕ) < #{j | x < m j} ↔ x < m i :=
    Tuple.lt_card_gt_iff_apply_gt_of_antitone hm
  constructor
  · intro h x
    have hshort : #{j | x < m j} ≤ n := by simpa using card_filter_le univ (fun j ↦ x < m j)
    have hlong : #{j | x < l j} ≤ n + 1 := by simpa using card_filter_le univ (fun j ↦ x < l j)
    constructor
    · by_contra! hbad
      let i : Fin n := ⟨#{j | x < l j}, hbad.trans_le hshort⟩
      have hi := (longer x i.castSucc).mpr
        (((shorter x i).mp hbad).trans_le (h.le_castSucc i))
      exact (lt_irrefl _ hi)
    · by_contra! hbad
      let i : Fin n := ⟨#{j | x < m j}, by omega⟩
      have hi := (shorter x i).mpr
        (((longer x i.succ).mp hbad).trans_le (h.succ_le i))
      exact (lt_irrefl _ hi)
  · intro h
    refine interlaces_iff.mpr fun i ↦ ⟨?_, ?_⟩
    · by_contra! hbad
      have hs := (shorter (l i.castSucc) i).mpr hbad
      have hl' := (longer (l i.castSucc) i.castSucc).mp (hs.trans_le (h _).1)
      exact (lt_irrefl _ hl')
    · by_contra! hbad
      have hs := (longer (m i) i.succ).mpr hbad
      have hm' : (i : ℕ) < #{j | m i < m j} := by
        have hh := (h (m i)).2
        simp only [Fin.val_succ] at hs
        omega
      exact lt_irrefl _ ((shorter (m i) i).mp hm')

/-- The branching exponent, the difference of the row sums, lies between the first and
last entries of the longer row. Neither row needs to be assumed sorted. -/
theorem Interlaces.sum_sub_sum_mem_Icc {n : ℕ} {l : Fin (n + 1) → ℤ} {m : Fin n → ℤ}
    (h : Interlaces l m) :
    (∑ i, l i) - ∑ i, m i ∈ Set.Icc (l (Fin.last n)) (l 0) := by
  constructor
  · rw [Fin.sum_univ_castSucc]
    have hs := sum_le_sum (fun i (_ : i ∈ univ) ↦ h.le_castSucc i)
    omega
  · rw [Fin.sum_univ_succ]
    have hs := sum_le_sum (fun i (_ : i ∈ univ) ↦ h.succ_le i)
    omega

end TauCeti
