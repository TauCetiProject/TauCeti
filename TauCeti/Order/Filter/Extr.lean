/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Extr

/-!
# Minima on sublevels and images

A minimum on a sublevel transfers to the full admissible set, and at a minimizer the sublevel at
the minimum value is exactly the set of all minimizers. Pullback objectives along a map `p` also
transfer `IsMinOn` and attained-minimum existence identically between `s` and `p '' s`.
-/

public section

open Set

namespace TauCeti

/-- A minimum on a sublevel is a minimum on the whole set, provided its value is
below the sublevel threshold. -/
theorem isMinOn_sublevel_iff {X β : Type*} [LinearOrder β] {f : X → β}
    {S : Set X} {u : X} {b : β} (hu : f u ≤ b) :
    IsMinOn f {x ∈ S | f x ≤ b} u ↔ IsMinOn f S u := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ h hx.1⟩
  by_cases hb : f x ≤ b
  · exact h ⟨hx, hb⟩
  · exact hu.trans (le_of_not_ge hb)

/-- A point `p z` minimizes `f` on `p '' s` if and only if `z` minimizes `f ∘ p` on `s`. -/
theorem isMinOn_image_iff {X Y β : Type*} [Preorder β] {p : X → Y} {f : Y → β}
    {s : Set X} {z : X} :
    IsMinOn f (p '' s) (p z) ↔ IsMinOn (f ∘ p) s z := by
  simp only [isMinOn_iff, forall_mem_image, Function.comp_apply]

/-- An attained minimum of `f` on `p '' s` exists if and only if an attained minimum of `f ∘ p`
on `s` exists. -/
theorem exists_mem_image_isMinOn_iff {X Y β : Type*} [Preorder β] {p : X → Y} {f : Y → β}
    {s : Set X} :
    (∃ y ∈ p '' s, IsMinOn f (p '' s) y) ↔ ∃ z ∈ s, IsMinOn (f ∘ p) s z := by
  simp only [exists_mem_image, isMinOn_image_iff]

end TauCeti

/-- At an admissible minimizer, the sublevel at its value is the full minimizer set. -/
theorem IsMinOn.minimizers_eq_sublevel {X β : Type*} [Preorder β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    {x ∈ S | IsMinOn f S x} = {x ∈ S | f x ≤ f u} := by
  ext x
  exact ⟨fun hx ↦ ⟨hx.1, hx.2 hu⟩,
    fun hx ↦ ⟨hx.1, fun y hy ↦ hx.2.trans (h hy)⟩⟩
