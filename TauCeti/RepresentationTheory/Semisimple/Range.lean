/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple

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
  have hsem := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
    (inferInstance : ρ.IsSemisimpleRepresentation)
  let σ := ρ.asAlgebraHom.rangeRestrict.toRingHom
  have : RingHomSurjective σ := ⟨AlgHom.rangeRestrict_surjective _⟩
  let e : ρ.asModule →ₛₗ[σ] V :=
    { ρ.asModuleEquiv.toAddEquiv.toAddMonoidHom with
      map_smul' := fun r v ↦ by
        simp [σ, Subalgebra.smul_def] }
  exact (e.isSemisimpleModule_iff_of_bijective ρ.asModuleEquiv.bijective).mp hsem

end Representation
