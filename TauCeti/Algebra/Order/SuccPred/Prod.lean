/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Group.Synonym
public import TauCeti.Order.SuccPred.Prod
import Mathlib.Algebra.Order.Group.Equiv

/-!
# Successors in lexicographic products of ordered additive monoids

In the lexicographic product `α ×ₗ β` of additive monoids where `β` is a successor order without
maximal elements, the least positive element `Order.succ (0 : α ×ₗ β)` lies in the second factor
(`(0, Order.succ 0)`), so every finite multiple `n • Order.succ (0 : α ×ₗ β)` has first
coordinate `0`. Consequently, any element `toLex (a, b)` with positive first coordinate `0 < a`
exceeds every `n • Order.succ 0` (`TauCeti.Order.nsmul_succ_zero_lt_toLex_of_pos`).
-/

public section

namespace TauCeti.Order

open _root_.Order

/-- Any positive first coordinate in `α ×ₗ β` strictly exceeds every finite multiple of the least
positive element `succ 0`. -/
theorem nsmul_succ_zero_lt_toLex_of_pos {α β : Type*} [AddMonoid α] [Preorder α]
    [AddMonoid β] [Preorder β] [SuccOrder β] [NoMaxOrder β] {a : α} (ha : 0 < a)
    (b : β) (n : ℕ) :
    n • succ (0 : α ×ₗ β) < toLex (a, b) := by
  have hfst : (ofLex (n • succ (0 : α ×ₗ β))).1 = 0 := by
    rw [← coe_ofLexAddEquiv (α × β), map_nsmul, ← AddMonoidHom.coe_fst, map_nsmul]
    simp
  exact Prod.Lex.lt_iff.2 (.inl (by simpa [hfst] using ha))

end TauCeti.Order
