/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.Atoms

import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice

/-!
# Superfluous elements of a lattice

An element is superfluous if every element that joins with it to give the top is already the top.
In a subobject lattice this describes the kernels of essential epimorphisms. The definition and
the lattice results generalize the superfluous submodule API.

## Reference

* R. Wisbauer, *Foundations of Module and Ring Theory* (1991), §19.1 and §19.3 (2)–(3).
-/

public section

namespace TauCeti

variable {α : Type*} [SemilatticeSup α] [OrderTop α]

/-- An element `a` is **superfluous** when every element `b` with `a ⊔ b = ⊤` is itself `⊤`. -/
def IsSuperfluous (a : α) : Prop :=
  ∀ b : α, a ⊔ b = ⊤ → b = ⊤

/-- The defining condition for a superfluous element. -/
theorem isSuperfluous_iff {a : α} : IsSuperfluous a ↔ ∀ b : α, a ⊔ b = ⊤ → b = ⊤ :=
  (Iff.rfl)

/-- If a superfluous element and a second element join to the top, the second is the top. -/
theorem IsSuperfluous.eq_top_of_sup_eq_top {a b : α} (ha : IsSuperfluous a)
    (h : a ⊔ b = ⊤) : b = ⊤ :=
  ha b h

/-- An element below a superfluous element is superfluous. -/
theorem IsSuperfluous.mono {a b : α} (hb : IsSuperfluous b) (hab : a ≤ b) :
    IsSuperfluous a := by
  intro c hc
  exact hb.eq_top_of_sup_eq_top (eq_top_mono (sup_le_sup_right hab c) hc)

/-- The join of two superfluous elements is superfluous. -/
theorem IsSuperfluous.sup {a b : α} (ha : IsSuperfluous a) (hb : IsSuperfluous b) :
    IsSuperfluous (a ⊔ b) := by
  intro c hc
  exact hb.eq_top_of_sup_eq_top (ha.eq_top_of_sup_eq_top (by simpa only [sup_assoc] using hc))

/-- A binary join is superfluous exactly when both elements are. -/
@[simp]
theorem isSuperfluous_sup_iff {a b : α} :
    IsSuperfluous (a ⊔ b) ↔ IsSuperfluous a ∧ IsSuperfluous b :=
  ⟨fun h ↦ ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h ↦ h.1.sup h.2⟩

/-- A superfluous element lies below every coatom. -/
theorem IsSuperfluous.le_coatom {a m : α} (ha : IsSuperfluous a) (hm : IsCoatom m) :
    a ≤ m := by
  by_contra h
  exact hm.1 (ha.eq_top_of_sup_eq_top (hm.2 _ (right_lt_sup.mpr h)))

/-- The bottom element is superfluous. -/
@[simp]
theorem isSuperfluous_bot [OrderBot α] : IsSuperfluous (⊥ : α) := by
  intro b h
  simpa only [bot_sup_eq] using h

/-- The top element is superfluous exactly when the order is a subsingleton. -/
@[simp]
theorem isSuperfluous_top_iff : IsSuperfluous (⊤ : α) ↔ Subsingleton α := by
  refine ⟨fun h ↦ ?_, fun _ b _ ↦ Subsingleton.elim b ⊤⟩
  have htop (a : α) : a = ⊤ := h.eq_top_of_sup_eq_top (top_sup_eq a)
  exact ⟨fun a b ↦ (htop a).trans (htop b).symm⟩

/-- The top element of a nontrivial lattice is not superfluous. -/
theorem not_isSuperfluous_top [Nontrivial α] : ¬ IsSuperfluous (⊤ : α) :=
  fun h ↦ not_subsingleton α (isSuperfluous_top_iff.mp h)

/-- A superfluous element of a nontrivial lattice is strictly below the top. -/
theorem IsSuperfluous.ne_top [Nontrivial α] {a : α} (ha : IsSuperfluous a) : a ≠ ⊤ :=
  fun h ↦ not_isSuperfluous_top (h ▸ ha)

/-- A superfluous element with a complement is the bottom element. -/
theorem IsSuperfluous.eq_bot_of_isCompl {β : Type*} [Lattice β] [BoundedOrder β] {a b : β}
    (ha : IsSuperfluous a) (hab : IsCompl a b) : a = ⊥ := by
  have hb := ha.eq_top_of_sup_eq_top hab.sup_eq_top
  simpa only [hb, inf_top_eq] using hab.inf_eq_bot

section CompleteLattice

variable {β : Type*} [CompleteLattice β]

/-- A finite supremum of superfluous elements is superfluous. -/
theorem isSuperfluous_iSup {ι : Sort*} [Finite ι] {a : ι → β}
    (ha : ∀ i, IsSuperfluous (a i)) : IsSuperfluous (⨆ i, a i) := by
  have := Fintype.ofFinite (PLift ι)
  rw [← iSup_plift_down, ← Finset.sup_univ_eq_iSup]
  exact Finset.sup_induction isSuperfluous_bot (fun _ hx _ hy ↦ hx.sup hy) fun i _ ↦ ha i.down

/-- A finite supremum is superfluous exactly when each element in the family is. -/
@[simp]
theorem isSuperfluous_iSup_iff {ι : Sort*} [Finite ι] {a : ι → β} :
    IsSuperfluous (⨆ i, a i) ↔ ∀ i, IsSuperfluous (a i) :=
  ⟨fun h i ↦ h.mono (le_iSup a i), isSuperfluous_iSup⟩

end CompleteLattice

end TauCeti

open TauCeti

/-- An order isomorphism preserves and reflects superfluous elements. -/
@[simp]
theorem OrderIso.isSuperfluous_iff {α β : Type*} [SemilatticeSup α] [OrderTop α]
    [SemilatticeSup β] [OrderTop β] (e : α ≃o β) (a : α) :
    IsSuperfluous (e a) ↔ IsSuperfluous a := by
  simp only [TauCeti.isSuperfluous_iff, e.surjective.forall, ← e.map_sup, ← e.map_top,
    e.injective.eq_iff]
