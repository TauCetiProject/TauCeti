/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Preorder.Finite

/-!
# Greatest and least elements of finite chains

A chain need not have a greatest element, and a finite set need not have one either, but a finite
chain always does: comparability upgrades a maximal element to a greatest one. Dually, a minimal
element of a finite chain is least.

For the `IsChain` lemmas the order is an arbitrary reflexive transitive `≤` rather than a
`Preorder`, matching the level of `Set.Finite.exists_maximal` and `Set.Finite.exists_minimal`, so
these results also apply to a relation carrying no `Preorder` instance. Every preorder supplies
both instances. The `Finset` lemma is stated for a `Preorder`.

## Main results

* `IsChain.exists_isGreatest`: a nonempty finite chain has a greatest element.
* `IsChain.exists_isLeast`: a nonempty finite chain has a least element.
* `Finset.exists_max_image_of_forall_comparable`: a nonempty finite set on which a function to a
  preorder takes pairwise comparable values has a point where the value is greatest.
-/

public section

namespace IsChain

variable {α : Type*} [LE α] [IsTrans α (· ≤ ·)] [Std.Refl (· ≤ · : α → α → Prop)] {s : Set α}

/-- A nonempty finite chain has a greatest element. -/
theorem exists_isGreatest (hchain : IsChain (· ≤ ·) s) (hfin : s.Finite) (hne : s.Nonempty) :
    ∃ a, IsGreatest s a := by
  obtain ⟨a, hmax⟩ := hfin.exists_maximal hne
  exact ⟨a, hmax.prop, fun b hb => (hchain.total hb hmax.prop).elim id (hmax.le_of_ge hb)⟩

/-- A nonempty finite chain has a least element. -/
theorem exists_isLeast (hchain : IsChain (· ≤ ·) s) (hfin : s.Finite) (hne : s.Nonempty) :
    ∃ a, IsLeast s a := by
  obtain ⟨a, hmin⟩ := hfin.exists_minimal hne
  exact ⟨a, hmin.prop, fun b hb => (hchain.total hmin.prop hb).elim id (hmin.le_of_le hb)⟩

end IsChain

namespace Finset

/-- On a nonempty finite set on which the values of `C` are pairwise comparable, some point has the
greatest value. -/
theorem exists_max_image_of_forall_comparable {α γ : Type*} [Preorder γ] (B : Finset α) (C : α → γ)
    (hC : ∀ a ∈ B, ∀ b ∈ B, C a ≤ C b ∨ C b ≤ C a) (hB : B.Nonempty) :
    ∃ t ∈ B, ∀ a ∈ B, C a ≤ C t := by
  have hchain : IsChain (· ≤ ·) (C '' (B : Set α)) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ -
    exact hC a ha b hb
  obtain ⟨_, ⟨t, ht, rfl⟩, hgreat⟩ :=
    hchain.exists_isGreatest (B.finite_toSet.image C) ((coe_nonempty.mpr hB).image C)
  exact ⟨t, ht, fun a ha => hgreat ⟨a, ha, rfl⟩⟩

end Finset
