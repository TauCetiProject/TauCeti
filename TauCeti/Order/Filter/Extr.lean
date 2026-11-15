/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Extr

/-!
# Minima on sublevels and conditionally complete lattices

A minimum on a sublevel transfers to the full admissible set. At an admissible minimizer, the
sublevel at the minimum value is the set of all minimizers, and in a conditionally complete
lattice that minimum value agrees with `sInf (f '' s)`.
-/

public section

open Set

/-- An admissible point minimizing `f` on `s` realizes the least element of `f '' s`. -/
theorem IsMinOn.isLeast_image {X β : Type*} [Preorder β] {f : X → β}
    {s : Set X} {a : X} (h : IsMinOn f s a) (ha : a ∈ s) :
    IsLeast (f '' s) (f a) :=
  ⟨mem_image_of_mem f ha, forall_mem_image.2 h⟩

/-- At an admissible minimizer, `sInf (f '' s)` equals the attained value. -/
theorem IsMinOn.csInf_image_eq {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {s : Set X} {a : X} (h : IsMinOn f s a) (ha : a ∈ s) :
    sInf (f '' s) = f a :=
  (h.isLeast_image ha).csInf_eq

/-- At an admissible minimizer, the sublevel at its value is the full minimizer set. -/
theorem IsMinOn.minimizers_eq_sublevel {X β : Type*} [Preorder β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    {x ∈ S | IsMinOn f S x} = {x ∈ S | f x ≤ f u} := by
  ext x
  exact ⟨fun hx ↦ ⟨hx.1, hx.2 hu⟩,
    fun hx ↦ ⟨hx.1, fun y hy ↦ hx.2.trans (h hy)⟩⟩

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

/-- On a nonempty set where `f` is bounded below, `a` minimizes `f` on `s` if and only if
`f a ≤ sInf (f '' s)`. -/
theorem isMinOn_iff_le_csInf_image {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {s : Set X} {a : X} (hs : s.Nonempty) (hbdd : BddBelow (f '' s)) :
    IsMinOn f s a ↔ f a ≤ sInf (f '' s) :=
  ⟨fun h ↦ le_csInf (hs.image f) (forall_mem_image.2 h),
    fun h _ hx ↦ h.trans (csInf_le hbdd (mem_image_of_mem f hx))⟩

/-- An admissible point `a ∈ s` minimizes `f` on `s` if and only if `f a = sInf (f '' s)`,
provided `f '' s` is bounded below. -/
theorem isMinOn_iff_eq_csInf_image {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {s : Set X} {a : X} (ha : a ∈ s) (hbdd : BddBelow (f '' s)) :
    IsMinOn f s a ↔ f a = sInf (f '' s) := by
  refine ⟨fun h ↦ (h.csInf_image_eq ha).symm, fun h ↦ ?_⟩
  rw [isMinOn_iff_le_csInf_image ⟨a, ha⟩ hbdd, h]

/-- On a nonempty set where `f` is bounded below, the set of admissible minimizers coincides
with the sublevel at `sInf (f '' s)`. -/
theorem minimizers_eq_sublevel_csInf {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {s : Set X} (hs : s.Nonempty) (hbdd : BddBelow (f '' s)) :
    {x ∈ s | IsMinOn f s x} = {x ∈ s | f x ≤ sInf (f '' s)} := by
  ext x
  exact and_congr_right fun _ ↦ isMinOn_iff_le_csInf_image hs hbdd

end TauCeti
