/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Order.RelIso.Basic

/-!
# Nearness: finite intervals of a relation

Two points `p` and `q` are near for a relation `r` (`TauCeti.IsNear r p q`) when the closed
interval between them, in either direction, is finite. For a linear order, nearness is the
relation whose classes are the finite condensation classes: `IsNear (· ≤ ·) p q` says that
`Set.uIcc p q` is finite (`TauCeti.isNear_le_iff`). Nearness is symmetric
(`TauCeti.isNear_comm`, `TauCeti.IsNear.symm`), reflexive for an antisymmetric relation
(`TauCeti.isNear_refl`), and transitive for a linear order (`TauCeti.IsNear.trans`), so it is an
equivalence relation for a linear order (`TauCeti.isNear_equivalence`). A relation isomorphism
preserves it (`RelIso.isNear_apply_iff`, `RelIso.setOf_isNear_apply`).
-/

public section

open Set

namespace TauCeti

variable {α β : Type*}

/-- Points `p` and `q` are **near** for a relation `r` when the closed interval between them, in
either direction, is finite. For a linear order, nearness is the relation of the condensation
classes. -/
def IsNear (r : α → α → Prop) (p q : α) : Prop :=
  {z | r p z ∧ r z q ∨ r q z ∧ r z p}.Finite

/-- Unfolds nearness: the closed interval between `p` and `q`, in either direction, is finite. -/
theorem isNear_iff {r : α → α → Prop} {p q : α} :
    IsNear r p q ↔ {z | r p z ∧ r z q ∨ r q z ∧ r z p}.Finite :=
  Iff.rfl

/-- Nearness is symmetric. -/
theorem isNear_comm {r : α → α → Prop} {p q : α} : IsNear r p q ↔ IsNear r q p := by
  simp only [isNear_iff, or_comm]

/-- Nearness is symmetric. -/
theorem IsNear.symm {r : α → α → Prop} {p q : α} (h : IsNear r p q) : IsNear r q p :=
  isNear_comm.1 h

/-- For an antisymmetric relation, every point is near itself: the only point between `p` and
`p` is `p`. -/
theorem isNear_refl (r : α → α → Prop) [Std.Antisymm r] (p : α) : IsNear r p p :=
  (finite_singleton p).subset fun _ hz ↦ by
    rcases hz with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> exact antisymm h₂ h₁

/-- For a linear order, `p` and `q` are near exactly when the unordered closed interval
`Set.uIcc p q` is finite. -/
theorem isNear_le_iff [LinearOrder α] {p q : α} : IsNear (· ≤ ·) p q ↔ (uIcc p q).Finite := by
  simp only [isNear_iff, ← mem_uIcc, ofPred_mem_eq]

/-- For a linear order, nearness is transitive, since `Set.uIcc p s` is covered by
`Set.uIcc p q` and `Set.uIcc q s`. -/
theorem IsNear.trans [LinearOrder α] {p q s : α} (h₁ : IsNear (· ≤ ·) p q)
    (h₂ : IsNear (· ≤ ·) q s) : IsNear (· ≤ ·) p s := by
  rw [isNear_le_iff] at *
  exact (h₁.union h₂).subset uIcc_subset_uIcc_union_uIcc

/-- For a linear order, nearness is an equivalence relation; its classes are the finite
condensation classes. -/
theorem isNear_equivalence [LinearOrder α] : Equivalence (IsNear (α := α) (· ≤ ·)) :=
  ⟨isNear_refl _, IsNear.symm, IsNear.trans⟩

end TauCeti

namespace RelIso

open TauCeti

variable {α β : Type*}

/-- A relation isomorphism `r ≃r r'` preserves nearness. -/
@[simp]
theorem isNear_apply_iff {r : α → α → Prop} {r' : β → β → Prop} (f : r ≃r r') (p q : α) :
    IsNear r' (f p) (f q) ↔ IsNear r p q := by
  have h : {z | r' (f p) z ∧ r' z (f q) ∨ r' (f q) z ∧ r' z (f p)} =
      f '' {z | r p z ∧ r z q ∨ r q z ∧ r z p} := by
    ext z
    obtain ⟨w, rfl⟩ := f.surjective z
    simp only [mem_ofPred_eq, f.map_rel_iff, f.injective.mem_set_image]
  rw [isNear_iff, isNear_iff, h, finite_image_iff f.injective.injOn]

/-- A relation isomorphism `f : r ≃r r'` carries the points near `p` to the points near `f p`. -/
theorem setOf_isNear_apply {r : α → α → Prop} {r' : β → β → Prop} (f : r ≃r r') (p : α) :
    {q | IsNear r' (f p) q} = f '' {q | IsNear r p q} := by
  ext q
  obtain ⟨w, rfl⟩ := f.surjective q
  simp only [mem_ofPred_eq, f.isNear_apply_iff, f.injective.mem_set_image]

end RelIso
