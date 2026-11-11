/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Module.Dual
public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.HopfAlgebra

/-!
# Contragredient actions of an enveloping algebra

The enveloping representation of the native dual Lie module is the Hopf
contragredient of the enveloping representation. Thus its action on a functional
is precomposition with the antipode action. This comparison lets integral
stability results for the Hopf action apply to the usual dual Lie module.

The constructions compared are `AlgHom.hopfDual` and
`TauCeti.UniversalEnvelopingAlgebra.representation`.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable (R L V : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup V] [Module R V] [LieRingModule L V] [LieModule R L V]

/-- The enveloping representation of the dual Lie module is the Hopf contragredient. -/
theorem representation_dual :
    representation R L (Module.Dual R V) = (representation R L V).hopfDual := by
  apply AlgHom.ext_of_adjoin_eq_top (s := Set.range (_root_.UniversalEnvelopingAlgebra.ι R))
    (adjoin_range_ι R L)
  rintro _ ⟨x, rfl⟩
  ext φ v
  simp only [representation_ι_apply, AlgHom.hopfDual_apply,
    hopfAlgebraStructAntipode_eq_antipode, _root_.UniversalEnvelopingAlgebra.antipode_ι,
    map_neg, LinearMap.neg_apply, Module.Dual.lie_apply]

end TauCeti.UniversalEnvelopingAlgebra

namespace UniversalEnvelopingAlgebra

open TauCeti.UniversalEnvelopingAlgebra

variable (R L V : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup V] [Module R V] [LieRingModule L V] [LieModule R L V]

/-- The dual Lie module's enveloping action is precomposition with the antipode action. -/
@[simp]
theorem representation_dual_apply (u : UniversalEnvelopingAlgebra R L)
    (φ : Module.Dual R V) (v : V) :
    representation R L (Module.Dual R V) u φ v =
      φ (representation R L V (HopfAlgebra.antipode R u) v) := by
  rw [representation_dual, AlgHom.hopfDual_apply]

end UniversalEnvelopingAlgebra
