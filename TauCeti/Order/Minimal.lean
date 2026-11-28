/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Minimal

/-!
# Minimality and maximality under order isomorphisms

Transport of `Minimal` and `Maximal` predicates along an order isomorphism `e : α ≃o β`
(`OrderIso.minimal_apply_iff`, `OrderIso.maximal_apply_iff`).
-/

public section

namespace OrderIso

/-- An order isomorphism transports minimality of a predicate along `e`. -/
@[to_dual /-- An order isomorphism transports maximality of a predicate along `e`. -/]
theorem minimal_apply_iff {α β : Type*} [LE α] [LE β] (e : α ≃o β)
    {p : α → Prop} {q : β → Prop} (hpq : ∀ x, q (e x) ↔ p x) (x : α) :
    Minimal q (e x) ↔ Minimal p x := by
  refine ⟨fun h ↦ ⟨(hpq x).mp h.prop, fun y hy hxy ↦ ?_⟩,
    fun h ↦ ⟨(hpq x).mpr h.prop, fun y hy hxy ↦ ?_⟩⟩
  · rw [← e.le_iff_le] at hxy ⊢
    exact h.le_of_le ((hpq y).mpr hy) hxy
  · obtain ⟨y, rfl⟩ := e.surjective y
    rw [e.le_iff_le] at hxy ⊢
    exact h.le_of_le ((hpq y).mp hy) hxy

end OrderIso
