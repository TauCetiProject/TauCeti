/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Scheme.Basic
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.ClosedImmersion

/-!
# Closed immersions of diagonalizable group schemes

A surjective homomorphism of finitely generated commutative character groups induces a
surjective map of their group algebras. Relative spectrum reverses this map, so the resulting
morphism of diagonalizable group schemes is a closed immersion.

## Main declarations

* `TauCeti.DiagonalizableGroup.isClosedImmersion_groupSchemeMap_of_surjective`: the
  contravariant diagonalizable-group image of a surjective character-group homomorphism is a
  closed immersion.
-/

public section

open CategoryTheory
open AlgebraicGeometry

namespace TauCeti

universe u

namespace DiagonalizableGroup

variable (R : Type u) [CommRing R]

/-- A surjective homomorphism of character groups induces a closed immersion of the associated
diagonalizable group schemes. -/
theorem isClosedImmersion_groupSchemeMap_of_surjective {G H : FGCommGrpCat.{u}} (φ : G ⟶ H)
    (hφ : Function.Surjective (FGCommGrpCat.toMonoidHom φ)) :
    IsClosedImmersion (groupSchemeMap R φ).hom.hom.left := by
  rw [groupSchemeMap_def,
    CommHopfAlgCat.isClosedImmersion_eqToHom_comp_hopfSpec_map_comp_eqToHom_iff
      (groupScheme_def R H) (groupScheme_def R G)]
  exact coordinateMap_surjective_of_surjective R φ hφ

end DiagonalizableGroup

end TauCeti
