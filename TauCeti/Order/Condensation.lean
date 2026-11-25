/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Basic

/-!
# Nearness: finite intervals of a relation

Two points `p` and `q` are near for a relation `r` (`TauCeti.IsNear r p q`) when the closed
interval between them, in either direction, is finite. For a linear order, nearness is the
relation whose classes are the finite condensation classes. Nearness is symmetric
(`TauCeti.isNear_comm`), and a bijection carrying one relation to another preserves it
(`TauCeti.isNear_map`, `TauCeti.setOf_isNear_map`).
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

/-- A bijection carrying `r` to `r'` preserves nearness. -/
theorem isNear_map {r : α → α → Prop} {r' : β → β → Prop} (f : α ≃ β)
    (hf : ∀ p q, r' (f p) (f q) ↔ r p q) (p q : α) : IsNear r' (f p) (f q) ↔ IsNear r p q := by
  have h : {z | r' (f p) z ∧ r' z (f q) ∨ r' (f q) z ∧ r' z (f p)} =
      f '' {z | r p z ∧ r z q ∨ r q z ∧ r z p} := by
    ext z
    obtain ⟨w, rfl⟩ := f.surjective z
    simp only [mem_ofPred_eq, hf, f.injective.mem_set_image]
  rw [isNear_iff, isNear_iff, h, finite_image_iff f.injective.injOn]

/-- A bijection carrying `r` to `r'` carries the points near `p` to the points near `f p`. -/
theorem setOf_isNear_map {r : α → α → Prop} {r' : β → β → Prop} (f : α ≃ β)
    (hf : ∀ p q, r' (f p) (f q) ↔ r p q) (p : α) :
    {q | IsNear r' (f p) q} = f '' {q | IsNear r p q} := by
  ext q
  obtain ⟨w, rfl⟩ := f.surjective q
  simp only [mem_ofPred_eq, isNear_map f hf, f.injective.mem_set_image]

end TauCeti
