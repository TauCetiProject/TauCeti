/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Extr

/-!
# Minima on sublevels and images, infimum values, and maxima attaining a bound

A minimum on a sublevel transfers to the full admissible set. At an admissible minimizer,
the sublevel at the minimum value is the set of all minimizers, and in a conditionally complete
lattice that value equals `sInf (f '' S)`. When an upper bound of a function is attained, the
global maximizers are exactly the points attaining it (`TauCeti.isMaxOn_univ_iff_eq`).
Pullback objectives along a map `p` also transfer `IsMinOn`, feasible minimizers, and
attained-minimum existence identically between `s` and `p '' s`.
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

/-- If some point attains an upper bound `M` of `f`, then `s` is a global maximizer of `f` exactly
when it attains `M`. -/
theorem isMaxOn_univ_iff_eq {X β : Type*} [PartialOrder β] {f : X → β} {M : β} {s : X}
    (hle : ∀ t, f t ≤ M) (hM : ∃ d, f d = M) : IsMaxOn f univ s ↔ f s = M :=
  ⟨fun h ↦ hM.elim fun d hd ↦ le_antisymm (hle s) (hd ▸ h (mem_univ d)), fun h t _ ↦ h ▸ hle t⟩

/-- At an admissible point of a set where `f` is bounded below, `IsMinOn f S u` holds
if and only if `f u` equals `sInf (f '' S)`. -/
theorem isMinOn_iff_eq_csInf {X β : Type*} [ConditionallyCompleteLattice β] {f : X → β}
    {S : Set X} {u : X} (hu : u ∈ S) (hb : BddBelow (f '' S)) :
    IsMinOn f S u ↔ f u = sInf (f '' S) :=
  ⟨fun h ↦ ((h.isGLB hu).csInf_eq ⟨f u, u, hu, rfl⟩).symm,
    fun h _ hx ↦ h ▸ csInf_le hb (mem_image_of_mem f hx)⟩

/-- A point `p z` minimizes `f` on `p '' s` if and only if `z` minimizes `f ∘ p` on `s`. -/
theorem isMinOn_image_iff {X Y β : Type*} [Preorder β] {p : X → Y} {f : Y → β}
    {s : Set X} {z : X} :
    IsMinOn f (p '' s) (p z) ↔ IsMinOn (f ∘ p) s z := by
  simp only [isMinOn_iff, forall_mem_image, Function.comp_apply]

/-- A point `z` is a feasible minimizer of `f ∘ p` on `s` if and only if `z ∈ s` and `p z` is a
feasible minimizer of `f` on `p '' s`. -/
theorem mem_and_isMinOn_comp_iff {X Y β : Type*} [Preorder β] {p : X → Y} {f : Y → β}
    {s : Set X} {z : X} :
    (z ∈ s ∧ IsMinOn (f ∘ p) s z) ↔ z ∈ s ∧ p z ∈ p '' s ∧ IsMinOn f (p '' s) (p z) := by
  rw [isMinOn_image_iff]
  exact ⟨fun ⟨hz, hmin⟩ ↦ ⟨hz, mem_image_of_mem p hz, hmin⟩, fun ⟨hz, _, hmin⟩ ↦ ⟨hz, hmin⟩⟩

/-- An attained minimum of `f` on `p '' s` exists if and only if an attained minimum of `f ∘ p`
on `s` exists. -/
theorem exists_mem_image_isMinOn_iff {X Y β : Type*} [Preorder β] {p : X → Y} {f : Y → β}
    {s : Set X} :
    (∃ y ∈ p '' s, IsMinOn f (p '' s) y) ↔ ∃ z ∈ s, IsMinOn (f ∘ p) s z := by
  simp only [exists_mem_image, isMinOn_image_iff]

/-- Along a surjection `p`, `z` minimizes `f ∘ p` on `univ` if and only if `p z` minimizes `f`
on `univ`. -/
theorem isMinOn_univ_comp_iff {X Y β : Type*} [Preorder β] {p : X → Y}
    (hp : Function.Surjective p) (f : Y → β) (z : X) :
    IsMinOn (f ∘ p) univ z ↔ IsMinOn f univ (p z) := by
  rw [← isMinOn_image_iff, image_univ, hp.range_eq]

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
