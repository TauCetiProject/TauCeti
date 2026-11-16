/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Extr

/-!
# Minima on sublevels, and maxima attaining a bound

A minimum on a sublevel transfers to the full admissible set. At a minimizer, the
sublevel at the minimum value is exactly the set of all minimizers. When an upper bound of a
function is attained, the global maximizers are exactly the points attaining it
(`TauCeti.isMaxOn_univ_iff_eq`).
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

end TauCeti

/-- At an admissible minimizer, the sublevel at its value is the full minimizer set. -/
theorem IsMinOn.minimizers_eq_sublevel {X β : Type*} [Preorder β] {f : X → β}
    {S : Set X} {u : X} (h : IsMinOn f S u) (hu : u ∈ S) :
    {x ∈ S | IsMinOn f S x} = {x ∈ S | f x ≤ f u} := by
  ext x
  exact ⟨fun hx ↦ ⟨hx.1, hx.2 hu⟩,
    fun hx ↦ ⟨hx.1, fun y hy ↦ hx.2.trans (h hy)⟩⟩
