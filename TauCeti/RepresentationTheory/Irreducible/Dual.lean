/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Irreducible

/-!
# Irreducibility of contragredient representations

For finite-dimensional group representations over a field, annihilators exchange
subrepresentations of a representation and of its contragredient.
-/

public section

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- The contragredient of a finite-dimensional irreducible group representation is
irreducible. -/
theorem IsIrreducible.dual {ρ : Representation k G V} (hρ : ρ.IsIrreducible) :
    ρ.dual.IsIrreducible := by
  have : Nontrivial V := hρ.nontrivial
  refine ⟨fun S ↦ ?_⟩
  have hS := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule)
  rcases eq_bot_or_eq_top S.dualCoannihilator with h | h
  · right
    apply Subrepresentation.toSubmodule_injective
    rw [← hS, ← Subrepresentation.toSubmodule_dualCoannihilator, h]
    simp
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [← hS, ← Subrepresentation.toSubmodule_dualCoannihilator, h]
    simp

end Representation
