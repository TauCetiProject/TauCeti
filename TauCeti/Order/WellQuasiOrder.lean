/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.WellQuasiOrder

/-!
# Well-foundedness of monotone pullbacks on well-quasi-orders

Pulling back the strict order of any preorder along a monotone map from a well-quasi-ordered
preorder yields a well-founded relation.

## Main results

* `Monotone.wellFounded_lt_comp`: if `β` is a well-quasi-ordered preorder and `c : β → α` is
  monotone into a preorder `α`, then `fun a b ↦ c a < c b` is well founded.
-/

public section

/-- Pulling back the strict order of a preorder along a monotone map from a well-quasi-ordered
preorder is well founded. -/
theorem Monotone.wellFounded_lt_comp {α β : Type*} [Preorder β] [WellQuasiOrderedLE β]
    [Preorder α] {c : β → α} (hc : Monotone c) :
    WellFounded fun a b : β ↦ c a < c b := by
  let e : (fun a b : β ↦ a ≤ b) →r fun a b : β ↦ c a ≤ c b := ⟨id, fun h ↦ hc h⟩
  have h_wqo : WellQuasiOrdered fun a b : β ↦ c a ≤ c b :=
    wellQuasiOrdered_le.of_surjective e Function.surjective_id
  simpa only [lt_iff_le_not_ge] using h_wqo.wellFounded
