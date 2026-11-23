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
* `Filter.le_of_eventually_le_and_le`: bounds `a ≤ f x ≤ b` holding eventually along a nontrivial
  filter force `a ≤ b`.
* `Filter.forall_mem_eventually_eq_of_forall_eventually_eq`: eventual isolation within a set
  along an indexed filter persists under any side predicate `R`.
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

/-- Isolation within `P` in `K` at `t₀` along a filter `l x` implies isolation within `P` in `K`
under any side predicate `R`. -/
theorem forall_mem_eventually_eq_of_forall_eventually_eq {ι : Type*} {P : Set (ι → α)}
    {K : Set α} {R : (ι → α) → Prop} {t₀ : ι} {l : (ι → α) → Filter α}
    (hiso : ∀ x ∈ P, (∀ t, x t ∈ K) →
      ∀ᶠ p in l x, ∀ y ∈ P, (∀ t, y t ∈ K) → y t₀ = p → y = x) :
    ∀ x ∈ P, (∀ t, x t ∈ K) → R x →
      ∀ᶠ p in l x, ∀ y ∈ P, (∀ t, y t ∈ K) → R y → y t₀ = p → y = x :=
  fun x hx hxK _ ↦ (hiso x hx hxK).mono fun _ hp y hy hyK _ ↦ hp y hy hyK

end Filter

namespace Equiv

variable {α β γ : Type*}

/-- The eventual form of `Equiv.symm_comp_eq`: `e.symm ∘ g` agrees with `f` along a filter exactly
when `g` agrees with `e ∘ f` there. -/
theorem symm_comp_eventuallyEq_iff (e : β ≃ γ) {l : Filter α} {f : α → β} {g : α → γ} :
    e.symm ∘ g =ᶠ[l] f ↔ g =ᶠ[l] e ∘ f :=
  Filter.eventually_congr <| .of_forall fun _ ↦ e.symm_apply_eq

end Equiv
