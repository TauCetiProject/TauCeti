/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Insertions at adjacent positions of a tuple

The positions `k.castSucc` and `k.succ` of `Fin (m + 1)` are adjacent: each one skips the other
to land on `k` (`Fin.succAbove_castSucc_self`, `Fin.succAbove_succ_self`). This file reads off
the entry of an insertion at one of them in the other position, and compares updating the two
insertions there.

## Main results

* `Fin.insertNth_castSucc_apply_succ` and `Fin.insertNth_succ_apply_castSucc`: after inserting at
  one of two adjacent positions, the other position holds the `k`-th entry of the tuple.
* `Fin.update_insertNth_castSucc`: inserting at `k.castSucc` and updating `k.succ` is inserting at
  `k.succ` and updating `k.castSucc`.
-/

public section

namespace Fin

variable {m : ℕ} {α : Sort*}

/-- After inserting at `k.castSucc`, the next position `k.succ` holds the `k`-th entry. -/
@[simp]
theorem insertNth_castSucc_apply_succ (k : Fin m) (u : α) (y : Fin m → α) :
    (k.castSucc.insertNth u y : Fin (m + 1) → α) k.succ = y k := by
  rw [← succAbove_castSucc_self, insertNth_apply_succAbove]

/-- After inserting at `k.succ`, the previous position `k.castSucc` holds the `k`-th entry. -/
@[simp]
theorem insertNth_succ_apply_castSucc (k : Fin m) (v : α) (y : Fin m → α) :
    (k.succ.insertNth v y : Fin (m + 1) → α) k.castSucc = y k := by
  rw [← succAbove_succ_self, insertNth_apply_succAbove]

/-- Two insertions at adjacent positions agree away from those positions. -/
theorem update_insertNth_castSucc (k : Fin m) (y : Fin m → α) (u v : α) :
    Function.update (k.castSucc.insertNth u y : Fin (m + 1) → α) k.succ v =
      Function.update (k.succ.insertNth v y : Fin (m + 1) → α) k.castSucc u := by
  have hk : k.castSucc ≠ k.succ := castSucc_lt_succ.ne
  ext l
  rcases lt_trichotomy l k.castSucc with h | rfl | h
  · rw [Function.update_of_ne (h.trans castSucc_lt_succ).ne, Function.update_of_ne h.ne,
      insertNth_apply_below h, insertNth_apply_below (h.trans castSucc_lt_succ)]
    simp
  · simp [hk]
  rcases eq_or_lt_of_le (castSucc_lt_iff_succ_le.1 h) with h' | h'
  · subst h'; simp [hk.symm]
  · rw [Function.update_of_ne h'.ne', Function.update_of_ne h.ne', insertNth_apply_above h,
      insertNth_apply_above h']
    simp

end Fin
