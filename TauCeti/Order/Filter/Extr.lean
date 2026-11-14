/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Extr

/-!
# Minima on sublevels and infimum values

A minimum on a sublevel transfers to the full admissible set. At an admissible minimizer,
the sublevel at the minimum value is the set of all minimizers, and in a conditionally complete
lattice that value equals `sInf (f '' S)`.
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

/-- At an admissible point of a set where `f` is bounded below, `IsMinOn f S u` holds
if and only if `f u` equals `sInf (f '' S)`. -/
theorem isMinOn_iff_eq_csInf {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {S : Set X} {u : X} (hu : u ∈ S) (hb : BddBelow (f '' S)) :
    IsMinOn f S u ↔ f u = sInf (f '' S) :=
  ⟨fun h ↦ ((h.isGLB hu).csInf_eq ⟨f u, u, hu, rfl⟩).symm,
    fun h _ hx ↦ h ▸ csInf_le hb (mem_image_of_mem f hx)⟩

end TauCeti

/-- At an admissible minimizer, the sublevel at its value is the full minimizer set. -/
theorem IsMinOn.minimizers_eq_sublevel {X β : Type*} [Preorder β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    {x ∈ S | IsMinOn f S x} = {x ∈ S | f x ≤ f u} := by
  ext x
  exact ⟨fun hx ↦ ⟨hx.1, hx.2 hu⟩,
    fun hx ↦ ⟨hx.1, fun y hy ↦ hx.2.trans (h hy)⟩⟩

/-- At an admissible minimizer, the infimum `sInf (f '' S)` equals its value. -/
theorem IsMinOn.csInf_eq {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    sInf (f '' S) = f u :=
  (h.isGLB hu).csInf_eq ⟨f u, u, hu, rfl⟩
