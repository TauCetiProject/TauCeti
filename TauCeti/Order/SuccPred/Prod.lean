/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.SuccPred.Basic

/-!
# Successors and predecessors in lexicographic products

In the lexicographic product `α ×ₗ β`, pairs are compared first by their first coordinate and then
by their second. When `β` has no maximal element, the successor of `(a, b)` is `(a, succ b)`, so
`α ×ₗ β` is a successor order. Dually, when `β` has no minimal element, `α ×ₗ β` is a predecessor
order with `pred (a, b) = (a, pred b)`.

In particular `ℤ ×ₗ ℤ` is a discretely ordered non-Archimedean abelian group whose least positive
element is `(0, 1)`, strictly smaller than `(1, 0)` and every positive multiple of it.
-/

public section

namespace Prod.Lex

open Order

variable {α β : Type*} [Preorder α] [Preorder β]

section Succ

variable [SuccOrder β] [NoMaxOrder β]

/-- When `β` has no maximal element, successors in `α ×ₗ β` are computed in the second
coordinate. -/
instance succOrder : SuccOrder (α ×ₗ β) where
  succ x := toLex ((ofLex x).1, succ (ofLex x).2)
  le_succ x := le_iff.2 (Or.inr ⟨rfl, le_succ (ofLex x).2⟩)
  max_of_succ_le {x} h := by
    rcases le_iff.1 h with hlt | ⟨-, hle⟩
    · exact (lt_irrefl _ hlt).elim
    · exact (not_isMax (ofLex x).2 (max_of_succ_le hle)).elim
  succ_le_of_lt {x y} h := by
    rcases lt_iff.1 h with hlt | ⟨heq, hlt⟩
    · exact le_iff.2 (Or.inl hlt)
    · exact le_iff.2 (Or.inr ⟨heq, succ_le_of_lt hlt⟩)

/-- The successor of a lexicographic pair advances its second coordinate. -/
@[simp]
theorem succ_toLex (a : α) (b : β) : succ (toLex (a, b)) = toLex (a, succ b) := (rfl)

end Succ

section Pred

variable [PredOrder β] [NoMinOrder β]

/-- When `β` has no minimal element, predecessors in `α ×ₗ β` are computed in the second
coordinate. -/
instance predOrder : PredOrder (α ×ₗ β) where
  pred x := toLex ((ofLex x).1, pred (ofLex x).2)
  pred_le x := le_iff.2 (Or.inr ⟨rfl, pred_le (ofLex x).2⟩)
  min_of_le_pred {x} h := by
    rcases le_iff.1 h with hlt | ⟨-, hle⟩
    · exact (lt_irrefl _ hlt).elim
    · exact (not_isMin (ofLex x).2 (min_of_le_pred hle)).elim
  le_pred_of_lt {x y} h := by
    rcases lt_iff.1 h with hlt | ⟨heq, hlt⟩
    · exact le_iff.2 (Or.inl hlt)
    · exact le_iff.2 (Or.inr ⟨heq, le_pred_of_lt hlt⟩)

/-- The predecessor of a lexicographic pair decrements its second coordinate. -/
@[simp]
theorem pred_toLex (a : α) (b : β) : pred (toLex (a, b)) = toLex (a, pred b) := (rfl)

end Pred

end Prod.Lex
