/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import TauCeti.Algebra.MonoidAlgebra.CosetBasis

/-!
# Faithful flatness of maps of group algebras

An injective homomorphism of commutative groups induces a faithfully flat map of group algebras
over any commutative ring. Over a nonzero commutative ring, the induced ring map is faithfully
flat exactly when the homomorphism is injective.
This is the coordinate-algebra criterion for faithful flatness of morphisms of diagonalizable
groups.
-/

public section

open MonoidAlgebra

namespace TauCeti.MonoidAlgebra

variable {G H : Type*} [CommGroup G] [CommGroup H]

/-- An injective homomorphism of commutative groups induces a faithfully flat group-algebra
map, including over the zero ring. -/
theorem faithfullyFlat_mapDomainRingHom_of_injective (k : Type*) [CommRing k]
    (p : G →* H) (hp : Function.Injective p) :
    (mapDomainRingHom k p).FaithfullyFlat := by
  let := (mapDomainRingHom k p).toAlgebra
  exact Module.FaithfullyFlat.of_linearEquiv _ _ (basisCosets k p hp).repr

/-- Over a nonzero commutative ring, the group-algebra map is faithfully flat exactly when
the homomorphism of character groups is injective. -/
@[simp]
theorem faithfullyFlat_mapDomainRingHom_iff (k : Type*) [CommRing k] [Nontrivial k]
    (p : G →* H) : (mapDomainRingHom k p).FaithfullyFlat ↔ Function.Injective p := by
  refine ⟨fun h x y hxy => ?_, faithfullyFlat_mapDomainRingHom_of_injective k p⟩
  apply single_left_injective (R := k) one_ne_zero
  apply h.injective
  simpa using congrArg (fun z => single z (1 : k)) hxy

end TauCeti.MonoidAlgebra
