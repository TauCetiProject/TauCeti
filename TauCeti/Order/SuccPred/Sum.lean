/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Sum.Order
public import Mathlib.Order.SuccPred.Basic

/-!
# Successors and predecessors in lexicographic sums

In the lexicographic sum `α ⊕ₗ β`, every element of `α` lies below every element of `β`. When `α`
has no maximal element, the successor of an element of either summand is its successor inside that
summand, so `α ⊕ₗ β` is a successor order. Dually, when `β` has no minimal element, `α ⊕ₗ β` is a
predecessor order with predecessors computed inside the summands. For example `ℤ ⊕ₗ ℤ`, two copies
of the integers one after the other, is a successor and predecessor order without endpoints that is
not isomorphic to `ℤ`.
-/

public section

namespace Sum.Lex

open Order

variable {α β : Type*} [Preorder α] [Preorder β]

section Succ

variable [SuccOrder α] [SuccOrder β] [NoMaxOrder α]

/-- When `α` has no maximal element, successors in `α ⊕ₗ β` are computed inside the summands. -/
instance succOrder : SuccOrder (α ⊕ₗ β) where
  succ x := Sum.elim (fun a => toLex (inl (succ a))) (fun b => toLex (inr (succ b))) (ofLex x)
  le_succ x := by
    rcases x with a | b
    · exact inl_le_inl_iff.mpr (le_succ a)
    · exact inr_le_inr_iff.mpr (le_succ b)
  max_of_succ_le {x} h := by
    rcases x with a | b
    · exact (not_isMax a (max_of_succ_le (inl_le_inl_iff.mp h))).elim
    · intro y hy
      rcases y with c | c
      · exact (not_inr_le_inl hy).elim
      · exact inr_le_inr_iff.mpr (max_of_succ_le (inr_le_inr_iff.mp h) (inr_le_inr_iff.mp hy))
  succ_le_of_lt {x y} h := by
    rcases x with a | b <;> rcases y with c | c
    · exact inl_le_inl_iff.mpr (succ_le_of_lt (inl_lt_inl_iff.mp h))
    · exact inl_le_inr _ _
    · exact (not_inr_lt_inl h).elim
    · exact inr_le_inr_iff.mpr (succ_le_of_lt (inr_lt_inr_iff.mp h))

/-- The successor of an element of the left summand is its successor there. -/
@[simp]
theorem succ_toLex_inl (a : α) : succ (toLex (inl a : α ⊕ β)) = toLex (inl (succ a)) := (rfl)

/-- The successor of an element of the right summand is its successor there. -/
@[simp]
theorem succ_toLex_inr (b : β) : succ (toLex (inr b : α ⊕ β)) = toLex (inr (succ b)) := (rfl)

end Succ

section Pred

variable [PredOrder α] [PredOrder β] [NoMinOrder β]

/-- When `β` has no minimal element, predecessors in `α ⊕ₗ β` are computed inside the summands. -/
instance predOrder : PredOrder (α ⊕ₗ β) where
  pred x := Sum.elim (fun a => toLex (inl (pred a))) (fun b => toLex (inr (pred b))) (ofLex x)
  pred_le x := by
    rcases x with a | b
    · exact inl_le_inl_iff.mpr (pred_le a)
    · exact inr_le_inr_iff.mpr (pred_le b)
  min_of_le_pred {x} h := by
    rcases x with a | b
    · intro y hy
      rcases y with c | c
      · exact inl_le_inl_iff.mpr (min_of_le_pred (inl_le_inl_iff.mp h) (inl_le_inl_iff.mp hy))
      · exact (not_inr_le_inl hy).elim
    · exact (not_isMin b (min_of_le_pred (inr_le_inr_iff.mp h))).elim
  le_pred_of_lt {x y} h := by
    rcases x with a | b <;> rcases y with c | c
    · exact inl_le_inl_iff.mpr (le_pred_of_lt (inl_lt_inl_iff.mp h))
    · exact inl_le_inr _ _
    · exact (not_inr_lt_inl h).elim
    · exact inr_le_inr_iff.mpr (le_pred_of_lt (inr_lt_inr_iff.mp h))

/-- The predecessor of an element of the left summand is its predecessor there. -/
@[simp]
theorem pred_toLex_inl (a : α) : pred (toLex (inl a : α ⊕ β)) = toLex (inl (pred a)) := (rfl)

/-- The predecessor of an element of the right summand is its predecessor there. -/
@[simp]
theorem pred_toLex_inr (b : β) : pred (toLex (inr b : α ⊕ β)) = toLex (inr (pred b)) := (rfl)

end Pred

end Sum.Lex
