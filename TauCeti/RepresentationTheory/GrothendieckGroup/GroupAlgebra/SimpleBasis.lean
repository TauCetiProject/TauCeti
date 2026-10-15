/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.SimpleBasis
public import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.OfModule

/-!
# Exhaustive simple families from irreducible representations

A classification of irreducible representations gives an exhaustive family of simple
group-algebra modules. This bridge lets simple-class bases use representation classifications
without repeating the transport from a module to its associated representation.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Monoid G] {I : Type w}

/-- A family of finitely generated group-algebra modules is exhaustive if the module attached
to every irreducible representation is isomorphic to a member of the family. No finiteness
assumption on the monoid or on the representations being classified is needed. -/
theorem isExhaustiveSimpleFamily_of_forall_isIrreducible
    (S : I → FGModuleCat.{max u v} k[G])
    (h : ∀ {V : Type (max u v)} [AddCommGroup V] [Module k V]
      (ρ : _root_.Representation k G V), ρ.IsIrreducible →
        ∃ i, Nonempty (ρ.asModule ≃ₗ[k[G]] S i)) :
    IsExhaustiveSimpleFamily S := by
  rw [isExhaustiveSimpleFamily_iff]
  intro M hM
  let := Module.restrictScalars k k[G] M
  let := IsScalarTower.restrictScalars k k[G] M
  obtain ⟨i, ⟨e⟩⟩ := h (_root_.Representation.ofModule' (k := k) (G := G) M)
    ((Representation.isIrreducible_ofModule'_iff M).mpr hM)
  exact ⟨i, ⟨(Representation.ofModule'AsModuleEquiv M).symm.trans e⟩⟩

end TauCeti
