/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Finset.Basic

/-!
# Cardinalities of nested closed intervals

A closed interval strictly inside another one in a locally finite preorder has strictly fewer
elements (`Finset.card_Icc_lt_card_Icc_right`, `Finset.card_Icc_lt_card_Icc_left`). This is the
decrease used to run strong induction on the size of `[a, b]`, as in the recursive definition of
the Möbius function.
-/

public section

namespace Finset

variable {α : Type*} [Preorder α] [LocallyFiniteOrder α] {a₁ a₂ b₁ b₂ : α}

/-- If `[a₁, b₁] ⊆ [a₂, b₂]` with one endpoint moved strictly inwards, then `[a₁, b₁]` has
strictly fewer elements. -/
@[to_dual (rename := a₁ ↔ b₁, a₂ ↔ b₂, ha ↔ hb) (reorder := ha hb) card_Icc_lt_card_Icc_right]
theorem card_Icc_lt_card_Icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) :
    #(Icc a₁ b₁) < #(Icc a₂ b₂) :=
  card_lt_card (Icc_ssubset_Icc_left hI ha hb)

end Finset
