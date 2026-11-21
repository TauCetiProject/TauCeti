/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.Basic
public import Mathlib.Data.Int.Cast.Basic

/-!
# Basic facts about filters

A filter is closed under binary intersections, so its members, ordered by inclusion, are
codirected.  Together with Mathlib's `Filter.inhabitedMem`, this lets the members of a filter
index a colimit, for instance the neighbourhoods `{U // U ∈ 𝓝ˢ A}ᵒᵈ` of a set ordered by reverse
inclusion.

## Main results

* `Filter.isCodirectedOrder_mem`: the members of a filter are codirected under inclusion.
* `Filter.le_of_eventually_le_and_le`: bounds `a ≤ f x ≤ b` holding eventually along a nontrivial
  filter force `a ≤ b`.
* `Filter.EventuallyLE.natCast_sub`: when one natural-valued function is eventually bounded by
  another along a filter, casting their subtraction agrees eventually with subtracting their casts.
* `Equiv.symm_comp_eventuallyEq_iff`: the eventual form of `Equiv.symm_comp_eq`, which moves an
  equivalence to the other side of an eventual equality.
-/

public section

namespace Filter

variable {α : Type*}

/-- The members of a filter are codirected under inclusion: the intersection of two members is a
member contained in both. -/
instance isCodirectedOrder_mem (f : Filter α) : IsCodirectedOrder {s : Set α // s ∈ f} :=
  ⟨fun s t ↦ ⟨⟨_, inter_mem s.property t.property⟩, Set.inter_subset_left, Set.inter_subset_right⟩⟩

/-- Bounds `a ≤ f x ≤ b` holding eventually along a nontrivial filter force `a ≤ b`. -/
theorem le_of_eventually_le_and_le {β : Type*} [Preorder β] {l : Filter α} [l.NeBot]
    {f : α → β} {a b : β} (h : ∀ᶠ x in l, a ≤ f x ∧ f x ≤ b) : a ≤ b :=
  let ⟨_, hx⟩ := h.exists
  hx.1.trans hx.2

namespace EventuallyLE

/-- When one natural-valued function is eventually bounded by another along a filter, casting
their subtraction to an `AddGroupWithOne` agrees eventually with subtracting their casts. -/
theorem natCast_sub {R : Type*} [AddGroupWithOne R] {l : Filter α}
    {f g : α → ℕ} (h : f ≤ᶠ[l] g) :
    (fun x ↦ ((g x - f x : ℕ) : R)) =ᶠ[l] fun x ↦ (g x : R) - (f x : R) :=
  h.mono fun _ hx ↦ Nat.cast_sub hx

end EventuallyLE

end Filter

namespace Equiv

variable {α β γ : Type*}

/-- The eventual form of `Equiv.symm_comp_eq`: `e.symm ∘ g` agrees with `f` along a filter exactly
when `g` agrees with `e ∘ f` there. -/
theorem symm_comp_eventuallyEq_iff (e : β ≃ γ) {l : Filter α} {f : α → β} {g : α → γ} :
    e.symm ∘ g =ᶠ[l] f ↔ g =ᶠ[l] e ∘ f :=
  Filter.eventually_congr <| .of_forall fun _ ↦ e.symm_apply_eq

end Equiv
