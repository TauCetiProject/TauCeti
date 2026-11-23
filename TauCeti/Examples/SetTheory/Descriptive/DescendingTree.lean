/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.SetTheory.Descriptive.Tree.Descending

/-!
# Regression examples: descending trees

These examples evaluate the rank formula `Descriptive.Tree.rank_descendingTree` on boundary cases:

* on an empty carrier the descending tree still contains the empty sequence, so its rank is `1`;
* the empty relation on `ℕ` has rank `2`: the empty sequence above the one-term sequences;
* the descending tree of `(ℕ, <)` has rank `ω + 1`, one more than the order type `ω`;
* the descending tree of `(ℕ, >)`, which is not well-founded, has a branch.
-/

open Descriptive Tree Ordinal

-- On an empty carrier the tree is `{[]}`, of rank `1`.
example (r : Empty → Empty → Prop) : rank (descendingTree r) = 1 := by
  have : WellFounded r := ⟨fun x => x.elim⟩
  rw [rank_descendingTree, ciSup_of_empty, Ordinal.bot_eq_zero, Order.succ_eq_add_one, zero_add]

-- The empty relation on `ℕ` gives rank `2`.
example : rank (descendingTree fun _ _ : ℕ => False) = 2 := by
  have : WellFounded (fun _ _ : ℕ => False) := ⟨fun _ => ⟨_, fun _ h => h.elim⟩⟩
  have h (x : ℕ) : WellFounded.rank (fun _ _ : ℕ => False) x = 0 := by
    rw [WellFounded.rank_eq]
    exact Ordinal.iSup_eq_zero_iff.2 fun b => b.property.elim
  simp only [rank_descendingTree, h, Order.succ_eq_add_one, zero_add, ciSup_const]
  exact one_add_one_eq_two

-- The descending tree of `(ℕ, <)` has rank `ω + 1`.
example : rank (descendingTree (α := ℕ) (· < ·)) = ω + 1 := by
  rw [rank_descendingTree, ← Order.succ_eq_add_one, ← iSup_natCast]
  congr 1
  refine le_antisymm (Ordinal.iSup_le fun n => ?_) (Ordinal.iSup_le fun n => ?_)
  · rw [congrFun (WellFounded.rank_eq_typein (α := ℕ) (· < ·)) n, typein_lt_nat,
      Order.succ_eq_add_one, ← Nat.cast_succ]
    exact Ordinal.le_iSup (fun m : ℕ => (m : Ordinal)) (n + 1)
  · have := Ordinal.le_iSup (fun m : ℕ => Order.succ (WellFounded.rank (α := ℕ) (· < ·) m)) n
    rw [congrFun (WellFounded.rank_eq_typein (α := ℕ) (· < ·)) n, typein_lt_nat] at this
    exact (Order.le_succ _).trans this

-- The descending tree of `(ℕ, >)` has the branch `0, 1, 2, …`.
example : ¬ IsWellFounded (descendingTree (α := ℕ) (· > ·)) :=
  not_isWellFounded_iff.2 ⟨id, (forall_ofFn_mem_descendingTree_iff id).2 fun n => n.lt_succ_self⟩
