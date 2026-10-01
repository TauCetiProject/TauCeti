/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Sym.Sym2
public import Mathlib.Order.Basic

/-!
# Unordered pairs and orders

In a preorder, an unordered pair of distinct comparable elements has at most one strictly
increasing representative. So the strictly increasing ordered pairs index unordered pairs
injectively, which is how off-diagonal unordered pairs of a linearly ordered type are enumerated.

## Main declarations

* `TauCeti.Sym2.injOn_mk_setOf_lt`: `Sym2.mk` is injective on the strictly increasing pairs.
-/

public section

namespace TauCeti.Sym2

variable {α : Type*} [Preorder α]

/-- `Sym2.mk` is injective on the strictly increasing ordered pairs. -/
theorem injOn_mk_setOf_lt : Set.InjOn (fun p : α × α => s(p.1, p.2)) {p | p.1 < p.2} := by
  rintro ⟨a, b⟩ (hab : a < b) ⟨c, d⟩ (hcd : c < d) h
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd (hab.trans hcd) (lt_irrefl _)

end TauCeti.Sym2
