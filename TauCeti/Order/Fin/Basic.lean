/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Order.Fin.Basic

/-!
# Order characterizations on `Fin`

This file characterizes elements of `Fin (k + 1)` by how they sit relative to the embedded indices
`i'.castSucc` (`i' : Fin k`).

## Main results

* `Fin.succ_eq_or_castSucc_eq_iff_forall_le`: an index `j : Fin (k + 1)` equals `i.succ` or
  `i.castSucc` if and only if `i` lies weakly above every `i'` with `i'.castSucc < j` and weakly
  below every `i'` with `j ≤ i'.castSucc`.
* `Fin.eq_iff_forall_castSucc_lt_and_le`: two indices `r, j : Fin (k + 1)` are equal if and only
  if they determine the same order cut on the embedded indices `i'.castSucc` (`i' : Fin k`).
-/

public section

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

end Fin
