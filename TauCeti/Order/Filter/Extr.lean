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
sublevel at the minimum value is the full set of minimizers, and in a conditionally complete
lattice the infimum of the image equals the attained value and characterizes minimizers when the
image is bounded below.
-/

public section

open Set

/-- At an admissible minimizer, the sublevel at its value is the full minimizer set. -/
theorem IsMinOn.minimizers_eq_sublevel {X β : Type*} [Preorder β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    {x ∈ S | IsMinOn f S x} = {x ∈ S | f x ≤ f u} := by
  ext x
  exact ⟨fun hx ↦ ⟨hx.1, hx.2 hu⟩,
    fun hx ↦ ⟨hx.1, fun _ hy ↦ hx.2.trans (h hy)⟩⟩

/-- An admissible minimizer realizes the least element of the image. -/
theorem IsMinOn.isLeast_image {X β : Type*} [Preorder β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    IsLeast (f '' S) (f u) :=
  ⟨mem_image_of_mem f hu, by rintro _ ⟨_, hx, rfl⟩; exact h hx⟩

/-- At an admissible minimizer, the infimum of the image equals the value there. -/
theorem IsMinOn.csInf_eq {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    sInf (f '' S) = f u :=
  (h.isLeast_image hu).csInf_eq

namespace TauCeti

/-- A minimum on a sublevel is a minimum on the whole set, provided its value is
below the sublevel threshold. -/
theorem isMinOn_sublevel_iff {X β : Type*} [LinearOrder β] {f : X → β}
    {S : Set X} {u : X} {b : β} (hu : f u ≤ b) :
    IsMinOn f {x ∈ S | f x ≤ b} u ↔ IsMinOn f S u := by
  refine ⟨fun h x hx ↦ ?_, fun h _ hx ↦ h hx.1⟩
  by_cases hb : f x ≤ b
  · exact h ⟨hx, hb⟩
  · exact hu.trans (le_of_not_ge hb)

/-- A point whose value is at most the infimum of a bounded-below image is a minimizer on the set,
whether or not the point belongs to the set. -/
theorem isMinOn_of_le_csInf {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {S : Set X} {u : X} (hb : BddBelow (f '' S)) (hu : f u ≤ sInf (f '' S)) :
    IsMinOn f S u :=
  fun _ hx ↦ hu.trans (csInf_le hb (mem_image_of_mem f hx))

/-- On a nonempty set with bounded-below image, `IsMinOn` is equivalent to bounding the infimum
from below. -/
theorem isMinOn_iff_le_csInf {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {S : Set X} {u : X} (hne : S.Nonempty) (hb : BddBelow (f '' S)) :
    IsMinOn f S u ↔ f u ≤ sInf (f '' S) :=
  ⟨fun h ↦ le_csInf (hne.image f) (by rintro _ ⟨_, hx, rfl⟩; exact h hx), isMinOn_of_le_csInf hb⟩

/-- At an admissible point when the image is bounded below, `IsMinOn` is equivalent to attaining
the infimum. -/
theorem isMinOn_iff_eq_csInf {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {S : Set X} {u : X} (hu : u ∈ S) (hb : BddBelow (f '' S)) :
    IsMinOn f S u ↔ f u = sInf (f '' S) :=
  ⟨fun h ↦ (h.csInf_eq hu).symm, fun h ↦ isMinOn_of_le_csInf hb h.le⟩

end TauCeti
