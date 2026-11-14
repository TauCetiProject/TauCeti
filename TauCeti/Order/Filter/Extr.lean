/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Extr

/-!
# Minima on sublevels and infimum characterizations

A minimum on a sublevel transfers to the full admissible set. At an admissible minimizer, the
sublevel at the minimum value is the full minimizer set, the attained value is the greatest lower
bound of the image, and in a conditionally complete lattice it equals `sInf` of the image.
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

/-- An admissible point minimizes `f` on `S` if and only if its value is a greatest lower bound of
`f '' S`. -/
theorem isMinOn_iff_isGLB {X β : Type*} [Preorder β] {f : X → β}
    {S : Set X} {u : X} (hu : u ∈ S) :
    IsMinOn f S u ↔ IsGLB (f '' S) (f u) :=
  ⟨IsMinOn.isGLB hu, fun h _ hx ↦ h.1 (mem_image_of_mem f hx)⟩

end TauCeti

/-- At an admissible minimizer, the sublevel at its value is the full minimizer set. -/
theorem IsMinOn.minimizers_eq_sublevel {X β : Type*} [Preorder β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    {x ∈ S | IsMinOn f S x} = {x ∈ S | f x ≤ f u} := by
  ext x
  exact ⟨fun hx ↦ ⟨hx.1, hx.2 hu⟩,
    fun hx ↦ ⟨hx.1, fun y hy ↦ hx.2.trans (h hy)⟩⟩

/-- At an admissible minimizer into a conditionally complete lattice, `sInf (f '' S)` equals the
attained value `f u`. -/
theorem IsMinOn.csInf_image_eq {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    sInf (f '' S) = f u :=
  (h.isGLB hu).csInf_eq ⟨f u, mem_image_of_mem f hu⟩

namespace TauCeti

/-- An admissible point minimizes `f` on `S` into a conditionally complete lattice if and only if
`f '' S` is bounded below and `f u = sInf (f '' S)`. -/
theorem isMinOn_iff_bddBelow_and_eq_csInf {X β : Type*} [ConditionallyCompleteLattice β]
    {f : X → β} {S : Set X} {u : X} (hu : u ∈ S) :
    IsMinOn f S u ↔ BddBelow (f '' S) ∧ f u = sInf (f '' S) :=
  ⟨fun h ↦ ⟨h.bddBelow, (h.csInf_image_eq hu).symm⟩,
    fun ⟨hb, heq⟩ _ hx ↦ heq ▸ csInf_le hb (mem_image_of_mem f hx)⟩

end TauCeti
