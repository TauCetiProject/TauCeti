/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Finset.Basic

/-!
# Cardinalities of nested closed intervals

Let `[a₂, b₂]` be a nonempty closed interval (`a₂ ≤ b₂`) of a locally finite preorder. If
`[a₁, b₁]` is obtained from it by moving neither endpoint outwards and one endpoint strictly
inwards, then `[a₁, b₁]` has strictly fewer elements (`Finset.card_Icc_lt_card_Icc_left`,
`Finset.card_Icc_lt_card_Icc_right`). These are the cardinality forms of Mathlib's
`Finset.Icc_ssubset_Icc_left` and `Finset.Icc_ssubset_Icc_right`.

This decrease drives strong induction on the size of `[a, b]`, as in the recursive definition of
the Möbius function `IncidenceAlgebra.mu` in `Mathlib.Combinatorics.Enumerative.IncidenceAlgebra`.
-/

public section

namespace Finset

variable {α : Type*} [Preorder α] [LocallyFiniteOrder α] {a₁ a₂ b₁ b₂ : α}

/-- If `[a₂, b₂]` is nonempty (`a₂ ≤ b₂`) and `[a₁, b₁]` is obtained from it by moving the left
endpoint strictly inwards (`a₂ < a₁`) and the right endpoint not outwards (`b₁ ≤ b₂`), then
`[a₁, b₁]` has strictly fewer elements than `[a₂, b₂]`. This is the cardinality form of
`Finset.Icc_ssubset_Icc_left`. -/
@[to_dual (rename := a₁ ↔ b₁, a₂ ↔ b₂, ha ↔ hb) (reorder := ha hb) card_Icc_lt_card_Icc_right
/-- If `[a₂, b₂]` is nonempty (`a₂ ≤ b₂`) and `[a₁, b₁]` is obtained from it by moving the left
endpoint not outwards (`a₂ ≤ a₁`) and the right endpoint strictly inwards (`b₁ < b₂`), then
`[a₁, b₁]` has strictly fewer elements than `[a₂, b₂]`. This is the cardinality form of
`Finset.Icc_ssubset_Icc_right`. -/]
theorem card_Icc_lt_card_Icc_left (hI : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) :
    #(Icc a₁ b₁) < #(Icc a₂ b₂) :=
  card_lt_card (Icc_ssubset_Icc_left hI ha hb)

end Finset
