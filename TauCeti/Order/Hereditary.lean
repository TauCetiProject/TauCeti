/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic

/-!
# Order-hereditary subsets

A subset-like carrier `s` of an ordered type with zero is *hereditary* (`TauCeti.IsHereditary`) if
`0 ≤ a ≤ b` and `b ∈ s` imply `a ∈ s`.

Every order-connected carrier containing `0` is hereditary (`TauCeti.IsHereditary.of_ordConnected`),
and the converse holds both for additive subgroups of a right-ordered additive group
(`TauCeti.isHereditary_iff_ordConnected`) and for carriers containing `0` whose elements are all
nonnegative (`TauCeti.isHereditary_iff_ordConnected_of_nonneg`).

## Main declarations

* `TauCeti.IsHereditary`: order-heredity predicate `0 ≤ a → a ≤ b → b ∈ s → a ∈ s` on any
  `SetLike` carrier, with `TauCeti.isHereditary_def`, `TauCeti.IsHereditary.mem_of_le`, and
  `TauCeti.isHereditary_congr`.
* `TauCeti.IsHereditary.of_ordConnected`, `TauCeti.isHereditary_iff_ordConnected`, and
  `TauCeti.isHereditary_iff_ordConnected_of_nonneg`: comparison with `Set.OrdConnected`.
-/

public section

namespace TauCeti

/-- A subset-like object `s` of an ordered type with zero is *hereditary* if `0 ≤ a ≤ b` and
`b ∈ s` imply `a ∈ s`. -/
def IsHereditary {S α : Type*} [SetLike S α] [Zero α] [LE α] (s : S) : Prop :=
  ∀ ⦃a b : α⦄, 0 ≤ a → a ≤ b → b ∈ s → a ∈ s

@[grind =]
theorem isHereditary_def {S α : Type*} [SetLike S α] [Zero α] [LE α] {s : S} :
    IsHereditary s ↔ ∀ ⦃a b : α⦄, 0 ≤ a → a ≤ b → b ∈ s → a ∈ s :=
  Iff.rfl

@[grind →]
theorem IsHereditary.mem_of_le {S α : Type*} [SetLike S α] [Zero α] [LE α] {s : S}
    (hs : IsHereditary s) {a b : α} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ∈ s) : a ∈ s :=
  hs ha hab hb

theorem isHereditary_congr {S₁ S₂ α : Type*} [SetLike S₁ α] [SetLike S₂ α] [Zero α] [LE α]
    {s₁ : S₁} {s₂ : S₂} (h : (s₁ : Set α) = (s₂ : Set α)) :
    IsHereditary s₁ ↔ IsHereditary s₂ := by
  simp only [isHereditary_def, ← SetLike.mem_coe, h]

/-- Every order-connected subset containing `0` is hereditary. -/
theorem IsHereditary.of_ordConnected {S α : Type*} [SetLike S α] [Zero α] [Preorder α]
    [ZeroMemClass S α] {s : S} (h : (s : Set α).OrdConnected) : IsHereditary s :=
  fun _ _ ha hab hb => h.out' (zero_mem s) hb ⟨ha, hab⟩

/-- For an additive subgroup of a right-ordered additive group, heredity coincides with order
connectedness. -/
theorem isHereditary_iff_ordConnected {S α : Type*} [SetLike S α] [AddGroup α]
    [Preorder α] [AddRightMono α] [AddSubgroupClass S α] {s : S} :
    IsHereditary s ↔ (s : Set α).OrdConnected := by
  refine ⟨fun hs => ⟨fun x hx y hy z hz => ?_⟩, fun h => IsHereditary.of_ordConnected (s := s) h⟩
  rw [SetLike.mem_coe] at hx hy ⊢
  have hsub : z - x ∈ s :=
    hs (sub_nonneg.mpr hz.1) (sub_le_sub_right hz.2 x) (sub_mem hy hx)
  simpa only [sub_add_cancel] using add_mem hsub hx

/-- For a subset containing `0` and consisting of nonnegative elements, heredity coincides with
order connectedness. -/
theorem isHereditary_iff_ordConnected_of_nonneg {S α : Type*} [SetLike S α] [Zero α] [Preorder α]
    [ZeroMemClass S α] {s : S} (hnonneg : ∀ x ∈ s, 0 ≤ x) :
    IsHereditary s ↔ (s : Set α).OrdConnected :=
  ⟨fun hs => ⟨fun _ hx _ hy _ hz => hs ((hnonneg _ hx).trans hz.1) hz.2 hy⟩,
    fun h => IsHereditary.of_ordConnected (s := s) h⟩

end TauCeti
