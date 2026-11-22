/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.SuccPred.Basic
import Mathlib.Algebra.Order.Group.Equiv

/-!
# Successors and predecessors in lexicographic products

In the lexicographic product `α ×ₗ β`, two pairs with the same first coordinate are compared in the
second coordinate, while a strict inequality in the first coordinate dominates every change in the
second. When `β` has no maximal element, the successor of `(a, b)` is `(a, succ b)`, so `α ×ₗ β`
is a successor order. Dually, when `β` has no minimal element, `α ×ₗ β` is a predecessor order with
`pred (a, b) = (a, pred b)`.

For example `ℤ ×ₗ ℤ`, equipped with componentwise addition, is a non-Archimedean discretely ordered
abelian group with least positive element `(0, 1)` and `(1, 0) > n • (0, 1)` for all `n : ℕ`
(`TauCeti.Order.nsmul_succ_zero_lt_toLex_of_pos`).
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
  le_succ _ := le_iff.mpr (.inr ⟨rfl, le_succ _⟩)
  max_of_succ_le {x} h := by
    rcases le_iff.mp h with hlt | ⟨_, hle⟩
    · exact (lt_irrefl _ hlt).elim
    · exact (not_isMax _ (max_of_succ_le hle)).elim
  succ_le_of_lt {x y} h := by
    rcases lt_iff.mp h with hlt | ⟨heq, hlt⟩
    · exact le_iff.mpr (.inl hlt)
    · exact le_iff.mpr (.inr ⟨heq, succ_le_of_lt hlt⟩)

/-- The successor of `toLex x` applies `succ` to the second coordinate. -/
@[simp]
theorem succ_toLex (x : α × β) : succ (toLex x) = toLex (x.1, succ x.2) := (rfl)

/-- Unwrapping `ofLex` after `succ` applies `succ` to the second coordinate. -/
@[simp]
theorem ofLex_succ (x : α ×ₗ β) : ofLex (succ x) = ((ofLex x).1, succ (ofLex x).2) := (rfl)

end Succ

section Pred

variable [PredOrder β] [NoMinOrder β]

/-- When `β` has no minimal element, predecessors in `α ×ₗ β` are computed in the second
coordinate. -/
instance predOrder : PredOrder (α ×ₗ β) where
  pred x := toLex ((ofLex x).1, pred (ofLex x).2)
  pred_le _ := le_iff.mpr (.inr ⟨rfl, pred_le _⟩)
  min_of_le_pred {x} h := by
    rcases le_iff.mp h with hlt | ⟨_, hle⟩
    · exact (lt_irrefl _ hlt).elim
    · exact (not_isMin _ (min_of_le_pred hle)).elim
  le_pred_of_lt {x y} h := by
    rcases lt_iff.mp h with hlt | ⟨heq, hlt⟩
    · exact le_iff.mpr (.inl hlt)
    · exact le_iff.mpr (.inr ⟨heq, le_pred_of_lt hlt⟩)

/-- The predecessor of `toLex x` applies `pred` to the second coordinate. -/
@[simp]
theorem pred_toLex (x : α × β) : pred (toLex x) = toLex (x.1, pred x.2) := (rfl)

/-- Unwrapping `ofLex` after `pred` applies `pred` to the second coordinate. -/
@[simp]
theorem ofLex_pred (x : α ×ₗ β) : ofLex (pred x) = ((ofLex x).1, pred (ofLex x).2) := (rfl)

end Pred

end Prod.Lex

namespace TauCeti.Order

open _root_.Order

/-- Any positive first coordinate in `α ×ₗ β` strictly exceeds every finite multiple of the least
positive element `succ 0`. -/
theorem nsmul_succ_zero_lt_toLex_of_pos {α β : Type*} [AddMonoid α] [Preorder α]
    [AddMonoid β] [Preorder β] [SuccOrder β] [NoMaxOrder β] {a : α} (ha : 0 < a)
    (b : β) (n : ℕ) :
    n • succ (0 : α ×ₗ β) < toLex (a, b) := by
  refine Prod.Lex.lt_iff.2 (.inl ?_)
  simpa [← coe_ofLexAddEquiv (α × β), ← AddMonoidHom.coe_fst, map_nsmul] using ha

end TauCeti.Order
