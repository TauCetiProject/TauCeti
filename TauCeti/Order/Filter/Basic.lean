/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Basic

/-!
# Basic facts about filters

A filter is closed under binary intersections, so its members, ordered by inclusion, are
codirected.  Together with Mathlib's `Filter.inhabitedMem`, this lets the members of a filter
index a colimit, for instance the neighbourhoods `{U // U ∈ 𝓝ˢ A}ᵒᵈ` of a set ordered by reverse
inclusion.

## Main results

* `Filter.isCodirectedOrder_mem`: the members of a filter are codirected under inclusion.
* `Equiv.symm_comp_eventuallyEq_iff`: the eventual form of `Equiv.symm_comp_eq`, which moves an
  equivalence to the other side of an eventual equality.
-/

public section

namespace Filter

variable {α : Type*}

/-- The members of a filter are codirected under inclusion: the intersection of two members is a
member contained in both. -/
instance isCodirectedOrder_mem (f : Filter α) : IsCodirectedOrder {s : Set α // s ∈ f} :=
  ⟨fun s t ↦ ⟨⟨_, inter_mem s.2 t.2⟩, Set.inter_subset_left, Set.inter_subset_right⟩⟩

end Filter

namespace Equiv

variable {α β γ : Type*}

/-- The eventual form of `Equiv.symm_comp_eq`: `e.symm ∘ g` agrees with `f` along a filter exactly
when `g` agrees with `e ∘ f` there. -/
theorem symm_comp_eventuallyEq_iff (e : β ≃ γ) {l : Filter α} {f : α → β} {g : α → γ} :
    e.symm ∘ g =ᶠ[l] f ↔ g =ᶠ[l] e ∘ f :=
  Filter.eventually_congr <| .of_forall fun _ ↦ e.symm_apply_eq

end Equiv
