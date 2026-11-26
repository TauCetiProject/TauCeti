/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.UpperLower.Basic

/-!
# Order characterizations on `Fin`

This file characterizes elements of `Fin (k + 1)` by how they sit relative to the embedded indices
`i'.castSucc` (`i' : Fin k`), and records that the embedded indices `Fin.castLE` form an initial
segment.

## Main results

* `Fin.succ_eq_or_castSucc_eq_iff_forall_le`: an index `j : Fin (k + 1)` equals `i.succ` or
  `i.castSucc` if and only if `i` lies weakly above every `i'` with `i'.castSucc < j` and weakly
  below every `i'` with `j ≤ i'.castSucc`.
* `Fin.eq_iff_forall_castSucc_lt_and_le`: two indices `r, j : Fin (k + 1)` are equal if and only
  if they determine the same order cut on the embedded indices `i'.castSucc` (`i' : Fin k`).
* `Fin.strictMono_of_forall_mem_Ioo`: a tuple separated by a sequence, `a k < w k < a (k + 1)`,
  is strictly increasing.
* `Fin.isLowerSet_range_castLE`: the image of `Fin.castLE` is an initial segment.
* `Fin.isLowerSet_iff_exists_eq_setOf_val_lt`: the lower sets of `Fin n` are the initial
  segments `{i | i < m}`.
-/

public section

open Set

namespace Fin

/-- An index `j : Fin (k + 1)` equals `i.succ` or `i.castSucc` if and only if `i` lies weakly
above every `i' : Fin k` with `i'.castSucc < j` and weakly below every `i' : Fin k` with
`j ≤ i'.castSucc`. -/
theorem succ_eq_or_castSucc_eq_iff_forall_le {k : ℕ} {i : Fin k} {j : Fin (k + 1)} :
    (i.succ = j ∨ i.castSucc = j) ↔
      (∀ i' : Fin k, i'.castSucc < j → i' ≤ i) ∧
        ∀ i' : Fin k, j ≤ i'.castSucc → i ≤ i' := by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨fun i' hi' ↦ castSucc_lt_succ_iff.mp hi',
        fun i' hi' ↦ castSucc_le_castSucc_iff.mp (i.castSucc_lt_succ.le.trans hi')⟩
    · exact ⟨fun i' hi' ↦ (castSucc_lt_castSucc_iff.mp hi').le,
        fun i' hi' ↦ castSucc_le_castSucc_iff.mp hi'⟩
  · rintro ⟨hlow, hhigh⟩
    rcases lt_trichotomy i.castSucc j with hij | hij | hij
    · have hij_val : i.val + 1 ≤ j.val := Nat.succ_le_of_lt (by simpa using lt_def.mp hij)
      rcases eq_or_lt_of_le hij_val with heq | hlt
      · exact Or.inl (eq_of_val_eq heq)
      · exfalso
        let i' : Fin k := ⟨i.val + 1, by omega⟩
        exact Nat.not_succ_le_self i.val (le_def.mp (hlow i' (lt_def.mpr hlt)))
    · exact Or.inr hij
    · exfalso
      let i' : Fin k := ⟨j.val, by omega⟩
      exact (not_le_of_gt hij) (castSucc_le_castSucc_iff.mpr (hhigh i' le_rfl))

/-- Two indices `r, j : Fin (k + 1)` are equal if and only if every `i' : Fin k` with
`i'.castSucc < j` satisfies `i'.castSucc < r` and every `i' : Fin k` with `j ≤ i'.castSucc`
satisfies `r ≤ i'.castSucc`. -/
theorem eq_iff_forall_castSucc_lt_and_le {k : ℕ} {r j : Fin (k + 1)} :
    r = j ↔
      (∀ i' : Fin k, i'.castSucc < j → i'.castSucc < r) ∧
        ∀ i' : Fin k, j ≤ i'.castSucc → r ≤ i'.castSucc := by
  constructor
  · rintro rfl
    exact ⟨fun _ h ↦ h, fun _ h ↦ h⟩
  · rintro ⟨hlow, hhigh⟩
    refine le_antisymm ?_ ?_
    · by_contra hlt
      replace hlt := lt_of_not_ge hlt
      let i' : Fin k := ⟨j.val, by omega⟩
      exact (not_le_of_gt hlt) (hhigh i' le_rfl)
    · by_contra hlt
      replace hlt := lt_of_not_ge hlt
      let i' : Fin k := ⟨r.val, by omega⟩
      exact (lt_irrefl r) (hlow i' hlt)

/-- A tuple `w` separated by a `ℤ`-indexed sequence `a`, in the sense that
`a k < w k < a (k + 1)` for every index `k`, is strictly increasing. -/
theorem strictMono_of_forall_mem_Ioo {α : Type*} [Preorder α] {n : ℕ} {w : Fin n → α}
    {a : ℤ → α} (h : ∀ k : Fin n, w k ∈ Ioo (a k) (a ((k : ℕ) + 1))) : StrictMono w := by
  obtain _ | n := n
  · exact fun i ↦ i.elim0
  · exact strictMono_iff_lt_succ.2 fun i ↦
      ((h i.castSucc).2.trans_le (le_of_eq (by simp))).trans (h i.succ).1

/-- The image of `Fin.castLE` is an initial segment of `Fin l`. -/
theorem isLowerSet_range_castLE {k l : ℕ} (h : k ≤ l) :
    IsLowerSet (Set.range (castLE h)) := by
  rw [range_castLE]
  exact fun _ _ hab hb ↦ lt_of_le_of_lt (le_iff_val_le_val.mp hab) hb

/-- The lower sets of `Fin n` are the initial segments `{i | i < m}`, for `m : ℕ`. -/
theorem isLowerSet_iff_exists_eq_setOf_val_lt {n : ℕ} {s : Set (Fin n)} :
    IsLowerSet s ↔ ∃ m : ℕ, s = {i : Fin n | (i : ℕ) < m} := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · rcases hs.eq_univ_or_Iio with rfl | ⟨a, rfl⟩
    · exact ⟨n, by ext i; simp⟩
    · exact ⟨a, by ext i; simp⟩
  · rintro ⟨m, rfl⟩ i j hji hi
    exact (le_def.1 hji).trans_lt hi

end Fin
