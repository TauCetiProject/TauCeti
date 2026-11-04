/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Equiv.Defs

/-!
# Equivalences carrying one set onto another

An equivalence `e : α ≃ β` carries `s` onto `t`, in the sense that `e x ∈ t ↔ x ∈ s` for every
`x`, exactly when `e` maps `s` into `t` and `e.symm` maps `t` into `s`.
-/

public section

namespace Equiv

/-- An equivalence carries `s` onto `t` exactly when it maps `s` into `t` and its inverse maps `t`
into `s`. -/
theorem forall_apply_mem_iff_iff_mapsTo {α β : Type*} (e : α ≃ β) (s : Set α) (t : Set β) :
    (∀ x, e x ∈ t ↔ x ∈ s) ↔ Set.MapsTo e s t ∧ Set.MapsTo e.symm t s :=
  ⟨fun h ↦ ⟨fun x hx ↦ (h x).mpr hx, fun y hy ↦ (h _).mp (by rwa [apply_symm_apply])⟩,
    fun ⟨h, hsymm⟩ x ↦ ⟨fun hx ↦ by simpa using hsymm hx, fun hx ↦ h hx⟩⟩

end Equiv
