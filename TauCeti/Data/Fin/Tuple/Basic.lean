/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Data.Set.Insert

/-!
# Insertions and appends in tuples

The positions `k.castSucc` and `k.succ` of `Fin (m + 1)` are adjacent: each one skips the other
to land on `k` (`Fin.succAbove_castSucc_self`, `Fin.succAbove_succ_self`). This file reads off
the entry of an insertion at one of them in the other position, and compares updating the two
insertions there. It also shows how `Fin.snoc` interacts with reindexing along a map extended to
send the last position to the last position. The image of an initial segment under `Fin.cons`
is obtained by inserting the first entry into the corresponding image for the tail.

## Main results

* `Fin.insertNth_castSucc_apply_succ` and `Fin.insertNth_succ_apply_castSucc`: after inserting at
  one of two adjacent positions, the other position holds the `k`-th entry of the tuple.
* `Fin.update_insertNth_castSucc`: inserting at `k.castSucc` and updating `k.succ` is inserting at
  `k.succ` and updating `k.castSucc`.
* `Fin.snoc_comp_snoc_castSucc_comp`: reindexing along `g` and then appending agrees with
  appending and then reindexing along the extension of `g` that fixes the last position.
* `Fin.tail_contractNth_succ`, `Fin.init_contractNth_castSucc`: contracting two adjacent entries
  away from the first (last) one commutes with dropping the first (last) entry.
* `Fin.tail_snoc`: dropping the first entry commutes with appending a last one.
* `Fin.snoc_tail_comp_rev`: appending the first entry to the reversed tail reverses the tuple.
* `Fin.contractNth_zero_cons`, `Fin.contractNth_succ_cons`: contracting entries of a tuple
  `Fin.cons x a`.
* `Fin.contractNth_castSucc_castSucc_snoc`, `Fin.contractNth_castSucc_last_snoc`: contracting
  entries of a tuple `Fin.snoc a x`.
* `Fin.init_contractNth_castSucc_last`: contracting the last two entries and dropping the last
  one drops the last two entries.
* `Fin.contractNth_last`: contracting at the last position drops the last entry.
* `Fin.contractNth_castSucc_castSucc_apply_last` and `Fin.contractNth_castSucc_last_apply_last`:
  the last entry of a contraction.
* `Fin.contractNth_castSucc_eq_update_removeNth_succ`: contracting the entries `j` and `j + 1`
  is deleting entry `j + 1` and then overwriting entry `j` by the contraction.
* `Fin.update_removeNth_succ_eq_removeNth_castSucc`: deleting entry `j + 1` and then overwriting
  entry `j` by the deleted entry is deleting entry `j`.
* `Fin.insertNth_one_ne_zero`: inserting the entry `1` gives a nonzero tuple.
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

/-- Appending `z` to `c` and reindexing along the extension of `g` that sends the last position
to the last position is the same as appending `z` to `c ∘ g`. -/
theorem snoc_comp_snoc_castSucc_comp {n : ℕ} (c : Fin n → α) (z : α) (g : Fin m → Fin n) :
    snoc c z ∘ snoc (castSucc ∘ g) (last n) = snoc (c ∘ g) z := by
  funext i
  exact lastCases (by simp) (fun j => by simp) i

/-- Dropping the first entry of `Fin.snoc a x` is appending `x` to the tail of `a`. -/
theorem tail_snoc {n : ℕ} (a : Fin (n + 1) → α) (x : α) :
    tail (snoc a x : Fin (n + 2) → α) = snoc (tail a) x := by
  conv_lhs => rw [← cons_self_tail a, ← cons_snoc_eq_snoc_cons, tail_cons]

/-- Appending the first entry of `a` to its reversed tail is reversing `a`. -/
theorem snoc_tail_comp_rev {α : Type*} {n : ℕ} (a : Fin (n + 1) → α) :
    snoc (tail a ∘ rev) (a 0) = a ∘ rev := by
  rw [← cons_comp_rev, cons_self_tail]

section ContractNth

variable {n : ℕ} (op : α → α → α)

/-- Contracting two adjacent entries after the first commutes with dropping the first entry. -/
theorem tail_contractNth_succ (j : Fin (n + 1)) (a : Fin (n + 2) → α) :
    tail (contractNth j.succ op a) = contractNth j op (tail a) := by
  funext k
  simp only [tail, contractNth, val_succ, Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff,
    succ_castSucc]

/-- Contracting two adjacent entries before the last commutes with dropping the last entry. -/
theorem init_contractNth_castSucc (j : Fin (n + 1)) (a : Fin (n + 2) → α) :
    init (contractNth j.castSucc op a) = contractNth j op (init a) := by
  funext k
  simp only [init, contractNth, val_castSucc, succ_castSucc]

/-- Contracting the first two entries of `Fin.cons x a` combines `x` with the first entry of `a`
under `op`. -/
theorem contractNth_zero_cons (x : α) (a : Fin (n + 1) → α) :
    contractNth 0 op (cons x a) = cons (op x (a 0)) (tail a) := by
  funext k
  cases k using Fin.cases with
  | zero => rfl
  | succ k => rfl

/-- Contracting two entries of `Fin.cons x a` other than the first contracts `a`. -/
theorem contractNth_succ_cons (j : Fin (n + 1)) (x : α) (a : Fin (n + 1) → α) :
    contractNth j.succ op (cons x a) = cons x (contractNth j op a) := by
  rw [← cons_self_tail (contractNth j.succ op (cons x a)), tail_contractNth_succ, tail_cons,
    contractNth_apply_of_lt _ _ _ _ (Nat.succ_pos _), castSucc_zero, cons_zero]

/-- Contracting the last two entries and dropping the last one drops the last two entries. -/
theorem init_contractNth_castSucc_last (a : Fin (n + 2) → α) :
    init (contractNth (last n).castSucc op a) = init (init a) := by
  funext k
  simp only [init, contractNth, val_castSucc, val_last, k.is_lt, ↓reduceIte]

/-- Contracting at the last position, which has no successor, drops the last entry. -/
@[simp]
theorem contractNth_last (a : Fin (n + 1) → α) : contractNth (last n) op a = init a := by
  funext k
  rw [contractNth_apply_of_lt _ _ _ _ (by simp), init]

/-- A contraction not involving the last entry keeps the last entry. -/
@[simp]
theorem contractNth_castSucc_castSucc_apply_last (j : Fin n) (a : Fin (n + 2) → α) :
    contractNth j.castSucc.castSucc op a (last n) = a (last (n + 1)) := by
  rw [contractNth_apply_of_gt _ _ _ _ (by simp [j.isLt]), succ_last]

/-- Contracting the last two entries makes their product the last entry. -/
@[simp]
theorem contractNth_castSucc_last_apply_last (a : Fin (n + 2) → α) :
    contractNth (last n).castSucc op a (last n) = op (a (last n).castSucc) (a (last (n + 1))) := by
  rw [contractNth_apply_of_eq _ _ _ _ (by simp), succ_last]

/-- Contracting two entries of `Fin.snoc a x` other than the last contracts `a`. -/
theorem contractNth_castSucc_castSucc_snoc (j : Fin n) (a : Fin (n + 1) → α) (x : α) :
    contractNth j.castSucc.castSucc op (snoc a x) = snoc (contractNth j.castSucc op a) x := by
  rw [← snoc_init_self (contractNth j.castSucc.castSucc op (snoc a x)),
    init_contractNth_castSucc, init_snoc, contractNth_castSucc_castSucc_apply_last, snoc_last]

/-- Contracting the last two entries of `Fin.snoc a x` combines the last entry of `a` with `x`
under `op`. -/
theorem contractNth_castSucc_last_snoc (a : Fin (n + 1) → α) (x : α) :
    contractNth (last n).castSucc op (snoc a x) = snoc (init a) (op (a (last n)) x) := by
  rw [← snoc_init_self (contractNth (last n).castSucc op (snoc a x)),
    init_contractNth_castSucc_last, init_snoc, contractNth_castSucc_last_apply_last,
    snoc_castSucc, snoc_last]

/-- Contracting the entries `j` and `j + 1` is deleting entry `j + 1` and then overwriting
entry `j` by the contraction. -/
theorem contractNth_castSucc_eq_update_removeNth_succ (j : Fin (n + 1)) (a : Fin (n + 2) → α) :
    contractNth j.castSucc op a =
      Function.update (removeNth j.succ a) j (op (a j.castSucc) (a j.succ)) := by
  funext k
  rcases lt_trichotomy k j with hkj | rfl | hkj
  · rw [Function.update_of_ne hkj.ne, contractNth_apply_of_lt _ _ _ _ hkj, removeNth_apply,
      succAbove_of_castSucc_lt _ _ (by simpa using hkj.le)]
  · rw [Function.update_self, contractNth_apply_of_eq _ _ _ _ rfl]
  · rw [Function.update_of_ne hkj.ne', contractNth_apply_of_gt _ _ _ _ hkj, removeNth_apply,
      succAbove_of_lt_succ _ _ (by simpa using hkj)]

end ContractNth

/-- Deleting entry `j + 1` and then overwriting entry `j` by the deleted entry is deleting
entry `j`. -/
theorem update_removeNth_succ_eq_removeNth_castSucc {n : ℕ} (j : Fin (n + 1))
    (a : Fin (n + 2) → α) :
    Function.update (removeNth j.succ a) j (a j.succ) = removeNth j.castSucc a := by
  funext k
  rcases lt_trichotomy k j with hkj | rfl | hkj
  · rw [Function.update_of_ne hkj.ne, removeNth_apply, removeNth_apply,
      succAbove_of_castSucc_lt _ _ (by simpa using hkj.le),
      succAbove_of_castSucc_lt _ _ (by simpa using hkj)]
  · rw [Function.update_self, removeNth_apply, succAbove_castSucc_self]
  · rw [Function.update_of_ne hkj.ne', removeNth_apply, removeNth_apply,
      succAbove_of_lt_succ _ _ (by simpa using hkj),
      succAbove_of_le_castSucc _ _ (by simpa using hkj.le)]

/-- The image of the first `n + 1` entries of a prepended tuple consists of its first entry
and the image of the first `n` entries of its tail. -/
@[simp]
theorem image_cons_le_eq_insert {α : Type*} {n : ℕ} (x : α) (p : Fin m → α) :
    Fin.cons x p '' {index | (index : ℕ) ≤ n} =
      insert x (p '' {index | (index : ℕ) < n}) := by
  ext element
  simp [Set.mem_image, Fin.exists_fin_succ, eq_comm, Nat.add_one_le_iff]

/-- Inserting the entry `1` into a tuple gives a tuple that does not vanish. -/
theorem insertNth_one_ne_zero {α : Type*} [Zero α] [One α] [NeZero (1 : α)] {n : ℕ}
    (i : Fin (n + 1)) (z : Fin n → α) : insertNth (α := fun _ ↦ α) i 1 z ≠ 0 :=
  fun h ↦ one_ne_zero (α := α) (by simpa using congr_fun h i)

end Fin
