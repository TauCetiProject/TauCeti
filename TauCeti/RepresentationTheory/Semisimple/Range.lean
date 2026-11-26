/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple

import TauCeti.RingTheory.SimpleModule.Basic

/-!
# Semisimplicity over the image algebra

A semisimple representation `ρ` makes its vector space a semisimple module over the image of
`ρ.asAlgebraHom`. This allows results about semisimple modules over algebras to be applied to
representations, for example to study their trace pairings or extension of scalars.
-/

public section

namespace Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- A semisimple representation is semisimple as a module over the image of its monoid-algebra
action. -/
theorem isSemisimpleModule_range_asAlgebraHom (ρ : Representation k G V)
    [ρ.IsSemisimpleRepresentation] : IsSemisimpleModule ρ.asAlgebraHom.range V := by
  rw [isSemisimpleRepresentation_iff_isSemisimpleModule_asModule] at *
  -- `ρ.asModule` is a type synonym for `V`; its monoid-algebra action factors through the range.
  let : Module ρ.asAlgebraHom.range ρ.asModule := (inferInstance : Module ρ.asAlgebraHom.range V)
  exact (RingHom.isSemisimpleModule_iff_of_surjective (M := ρ.asModule)
    ρ.asAlgebraHom.rangeRestrict.toRingHom (AlgHom.rangeRestrict_surjective _)
    fun _ _ ↦ rfl).mp ‹_›

end Representation
