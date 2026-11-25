/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.ExistsUnique
public import Mathlib.Basic.Logic.Basic

/-!
# Unique existence among two points

A predicate holds at exactly one of two distinct points exactly when it holds at one of them but
not at the other (`TauCeti.existsUnique_and_eq_or_eq_iff_xor`). This is the form in which a vertex
lying in exactly two edges is covered exactly once.
-/

public section

namespace TauCeti

/-- A predicate holds at exactly one of two distinct points `x` and `y` exactly when it holds at
one of them but not at the other. -/
theorem existsUnique_and_eq_or_eq_iff_xor {α : Sort*} {p : α → Prop} {x y : α} (hxy : x ≠ y) :
    (∃! a, p a ∧ (a = x ∨ a = y)) ↔ Xor (p x) (p y) := by
  constructor
  · rintro ⟨a, ⟨ha, rfl | rfl⟩, huniq⟩
    · exact Or.inl ⟨ha, fun hy => hxy (huniq y ⟨hy, Or.inr rfl⟩).symm⟩
    · exact Or.inr ⟨ha, fun hx => hxy (huniq x ⟨hx, Or.inl rfl⟩)⟩
  · rintro (⟨hx, hy⟩ | ⟨hy, hx⟩)
    · refine ⟨x, ⟨hx, Or.inl rfl⟩, fun a ⟨ha, hax⟩ => ?_⟩
      rcases hax with rfl | rfl
      · rfl
      · exact absurd ha hy
    · refine ⟨y, ⟨hy, Or.inr rfl⟩, fun a ⟨ha, hay⟩ => ?_⟩
      rcases hay with rfl | rfl
      · exact absurd ha hx
      · rfl

end TauCeti
