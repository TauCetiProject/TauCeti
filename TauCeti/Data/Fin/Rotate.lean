/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Ring
import TauCeti.Data.Fin.Basic

/-!
# Cyclic rotation of finite block indices

The equivalence between pairs of finite ordinals and a single finite ordinal lists the pairs
in blocks. These lemmas describe the successor within each block and across its boundary.
Appending the next block's head to a block displays this succession on the tuple entries.
-/

public section

namespace Fin

-- The packed-index rules take precedence over the generic rewrite `finRotate_apply`.
/-- Cyclic rotation of the index of a pair advances its second coordinate inside a block. -/
@[simp↓]
theorem finRotate_finProdFinEquiv_castSucc {r k : ℕ} (a : Fin r) (t : Fin k) :
    finRotate (r * (k + 1)) (finProdFinEquiv (a, t.castSucc)) =
      finProdFinEquiv (a, t.succ) := by
  have h : (finProdFinEquiv (a, t.castSucc) : Fin (r * (k + 1))).val + 1 < r * (k + 1) := by
    have ha := (finProdFinEquiv (a, t.succ) : Fin (r * (k + 1))).isLt
    simpa [finProdFinEquiv, add_right_comm] using ha
  apply Fin.ext
  rw [Fin.coe_finRotate_of_add_one_lt h]
  simp [finProdFinEquiv, add_right_comm]

/-- At the last index of a block, cyclic rotation advances to the first index of the next block. -/
@[simp↓]
theorem finRotate_finProdFinEquiv_last {r k : ℕ} (a : Fin r) :
    finRotate (r * (k + 1)) (finProdFinEquiv (a, Fin.last k)) =
      finProdFinEquiv (finRotate r a, (0 : Fin (k + 1))) := by
  apply Fin.ext
  simp only [Fin.coe_finRotate_eq_ite, finProdFinEquiv, Equiv.coe_fn_mk, Fin.val_last,
    Fin.val_zero, zero_add]
  have hstep : k + (k + 1) * a.val + 1 = (a.val + 1) * (k + 1) := by ring
  rw [hstep]
  have hcancel : (a.val + 1) * (k + 1) = r * (k + 1) ↔ a.val + 1 = r :=
    Nat.mul_left_inj (Nat.succ_ne_zero k)
  simp only [hcancel]
  split_ifs <;> simp [mul_comm]

/-- If each block is extended by the head of the next block, the entry after any position
in that block is the entry of the original tuple at the cyclic successor of that position. -/
@[simp↓]
theorem snoc_finProdFinEquiv_succ {α : Type*} {r k : ℕ}
    (u : Fin (r * (k + 1)) → α) (a : Fin r) (t : Fin (k + 1)) :
    snoc (α := fun _ ↦ α) (fun j ↦ u (finProdFinEquiv (a, j)))
        (u (finProdFinEquiv (finRotate r a, 0))) t.succ =
      u (finRotate (r * (k + 1)) (finProdFinEquiv (a, t))) := by
  induction t using lastCases with
  | last =>
    rw [finRotate_finProdFinEquiv_last, succ_last, snoc_last]
  | cast t =>
    rw [finRotate_finProdFinEquiv_castSucc, succ_castSucc, snoc_castSucc]

end Fin
