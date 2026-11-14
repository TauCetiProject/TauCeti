/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Extr

/-!
# Minima on sublevels and infima of images

A minimum on a sublevel transfers to the full admissible set. At a minimizer, the
sublevel at the minimum value is exactly the set of all minimizers, its value is the least
element of the image, and in a conditionally complete lattice it agrees with `sInf` of the image.
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

end TauCeti

/-- At an admissible minimizer, the sublevel at its value is the full minimizer set. -/
theorem IsMinOn.minimizers_eq_sublevel {X β : Type*} [Preorder β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    {x ∈ S | IsMinOn f S x} = {x ∈ S | f x ≤ f u} := by
  ext x
  exact ⟨fun hx ↦ ⟨hx.1, hx.2 hu⟩,
    fun hx ↦ ⟨hx.1, fun y hy ↦ hx.2.trans (h hy)⟩⟩

/-- At an admissible minimizer, the value is the least element of the image. -/
theorem IsMinOn.isLeast_image {X β : Type*} [Preorder β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    IsLeast (f '' S) (f u) :=
  ⟨mem_image_of_mem f hu, by rintro _ ⟨x, hx, rfl⟩; exact h hx⟩

/-- At an admissible minimizer in a conditionally complete lattice, the infimum of the image
is the minimum value. -/
theorem IsMinOn.csInf_image_eq {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    sInf (f '' S) = f u :=
  (h.isLeast_image hu).csInf_eq

namespace TauCeti

/-- On a set whose image is bounded below in a conditionally complete lattice, an admissible
point minimizes `f` if and only if its value equals `sInf (f '' S)`. -/
theorem isMinOn_iff_eq_csInf_image {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {S : Set X} {u : X} (hu : u ∈ S) (hbdd : BddBelow (f '' S)) :
    IsMinOn f S u ↔ f u = sInf (f '' S) :=
  ⟨fun h ↦ (h.csInf_image_eq hu).symm,
    fun heq _ hx ↦ heq.le.trans (csInf_le hbdd (mem_image_of_mem f hx))⟩

end TauCeti
