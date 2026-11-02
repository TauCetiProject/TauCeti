/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.List

/-!
# Permutations of `Fin n`

This file supplements Mathlib's `Mathlib.GroupTheory.Perm.Fin`.

## Main results

* `Fin.coe_cycleRange`: the value of the cycle `Fin.cycleRange i = (0 1 ⋯ i)` at `j`, as a
  natural number, read off the comparison of the values of `j` and `i`. Unlike
  `Fin.cycleRange_apply` it needs no `NeZero n` instance, and both its case split and its result
  are stated on natural numbers, ready for `omega`.
* `List.formPerm_finRange`, `Fin.formPerm_sort_univ`: the cycle through the points of `Fin n` in
  increasing order is the rotation `finRotate n`, that is `i ↦ i + 1` modulo `n`.
-/

public section

namespace Fin

/-- The value of the cycle `(0 1 ⋯ i)` at `j`: one more than `j` below `i`, `0` at `i`, and `j`
above `i`. -/
theorem coe_cycleRange {n : ℕ} (i j : Fin n) :
    (cycleRange i j : ℕ) = if (j : ℕ) < i then (j : ℕ) + 1 else if (j : ℕ) = i then 0 else j := by
  rcases le_or_gt j i with h | h
  · rw [coe_cycleRange_of_le h]
    have h' : (j : ℕ) ≤ i := h
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  · rw [cycleRange_of_gt h]
    have h' : (i : ℕ) < j := h
    split_ifs <;> omega

/-- The cycle through the points of `Fin n` in increasing order is the rotation `i ↦ i + 1`
modulo `n`. -/
@[simp]
theorem _root_.List.formPerm_finRange (n : ℕ) : (List.finRange n).formPerm = finRotate n := by
  ext x
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := x.pos; omega⟩
  have hx : (List.finRange (m + 1))[(x : ℕ)]'(by simp [x.isLt]) = x := by simp
  rw [← hx, List.formPerm_apply_getElem _ (List.nodup_finRange _)]
  simp only [List.getElem_finRange, Fin.val_cast, List.length_finRange, coe_finRotate, Fin.ext_iff,
    Fin.val_last]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The cycle through the points of `Fin n`, enumerated in increasing order by `Finset.sort`, is
the rotation `i ↦ i + 1` modulo `n`. -/
@[simp]
theorem formPerm_sort_univ (n : ℕ) :
    (Finset.univ : Finset (Fin n)).sort.formPerm = finRotate n := by
  rw [sort_univ, List.formPerm_finRange]

end Fin
