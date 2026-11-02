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
* `finAddFlip_trans_finCongr_eq_finRotate_pow`, `sign_finAddFlip_trans_finCongr`: exchanging the
  blocks of the first `m` and the last `n` points of `Fin (m + n)` is the rotation by `n`, of sign
  `(-1) ^ (m * n)`. This is the sign incurred by exchanging the factors of a product orientation.
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

/-- The `k`-th power of the rotation `finRotate n` adds `k` modulo `n`. -/
theorem _root_.coe_finRotate_pow (n k : ℕ) (i : Fin n) :
    (((finRotate n ^ k) i : Fin n) : ℕ) = (i + k) % n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
      ← Nat.add_mod, Nat.add_assoc]

/-- Exchanging the blocks of the first `m` and the last `n` points of `Fin (m + n)`, that is,
`finAddFlip` read back in `Fin (m + n)`, is the rotation `i ↦ i + n` modulo `m + n`. -/
theorem _root_.finAddFlip_trans_finCongr_eq_finRotate_pow (m n : ℕ) :
    (finAddFlip.trans (finCongr (add_comm n m)) : Equiv.Perm (Fin (m + n))) =
      finRotate (m + n) ^ n := by
  ext k
  rw [coe_finRotate_pow]
  refine Fin.addCases (fun i ↦ ?_) (fun j ↦ ?_) k
  · simp only [Equiv.trans_apply, finAddFlip_apply_castAdd, finCongr_apply, Fin.val_cast,
      Fin.val_natAdd, Fin.val_castAdd]
    rw [Nat.mod_eq_of_lt (by omega), Nat.add_comm]
  · simp only [Equiv.trans_apply, finAddFlip_apply_natAdd, finCongr_apply, Fin.val_cast,
      Fin.val_castAdd, Fin.val_natAdd]
    rw [show m + j + n = j + (m + n) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Exchanging the blocks of the first `m` and the last `n` points of `Fin (m + n)` has sign
`(-1) ^ (m * n)`. -/
@[simp]
theorem _root_.sign_finAddFlip_trans_finCongr (m n : ℕ) :
    Equiv.Perm.sign (finAddFlip.trans (finCongr (add_comm n m)) : Equiv.Perm (Fin (m + n))) =
      (-1) ^ (m * n) := by
  rw [finAddFlip_trans_finCongr_eq_finRotate_pow, map_pow, sign_finRotate, ← pow_mul]
  rcases n with _ | n
  · simp
  · rw [show (m + (n + 1) - 1) * (n + 1) = m * (n + 1) + n * (n + 1) by
      rw [show m + (n + 1) - 1 = m + n by omega]; ring, pow_add,
      (Nat.even_mul_succ_self n).neg_one_pow, mul_one]

end Fin
