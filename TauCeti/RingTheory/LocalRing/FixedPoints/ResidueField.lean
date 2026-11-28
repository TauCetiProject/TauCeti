/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import TauCeti.RingTheory.LocalRing.FixedPoints.Basic
import TauCeti.RingTheory.LocalRing.RingHom.Subalgebra

/-!
# Residue-field separability for fixed-point subalgebras of local rings

Separability of `ResidueField B / ResidueField A` along a local homomorphism `A → B` descends to
`ResidueField B / ResidueField B^G` (`isSeparable_residueField_fixedPoints_subalgebra`) and
`ResidueField B^H / ResidueField B^G` (`isSeparable_residueField_fixedPoints_subalgebra_of_le`).
-/

public section
namespace TauCeti

/-- If a local homomorphism `A → B` has separable residue extension and `G` acts on `B` over `A`,
then the residue extension of `B^G → B` is separable. -/
theorem isSeparable_residueField_fixedPoints_subalgebra (A B G : Type*) [CommRing A]
    [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
    Algebra.IsSeparable (IsLocalRing.ResidueField (FixedPoints.subalgebra A B G))
      (IsLocalRing.ResidueField B) :=
  Algebra.isSeparable_tower_top_of_isSeparable (IsLocalRing.ResidueField A)
    (IsLocalRing.ResidueField (FixedPoints.subalgebra A B G)) (IsLocalRing.ResidueField B)

/-- If a local homomorphism `A → B` has separable residue extension and `G` acts on `B` over `A`,
then for any submonoid-like subobject `H` of `G` the residue extension of `B^G → B^H` is
separable. -/
theorem isSeparable_residueField_fixedPoints_subalgebra_of_le (A B : Type*) {G S : Type*}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    [SetLike S G] [SubmonoidClass S G] (H : S) :
    letI := fixedPointsSubalgebraAlgebra A B H
    letI := isLocalHom_algebraMap_fixedPoints_subalgebra A B H
    Algebra.IsSeparable (IsLocalRing.ResidueField (FixedPoints.subalgebra A B G))
      (IsLocalRing.ResidueField (FixedPoints.subalgebra A B H)) :=
  let _ := fixedPointsSubalgebraAlgebra A B H
  let _ := isScalarTower_fixedPoints_subalgebra A B H
  let _ := isLocalHom_algebraMap_fixedPoints_subalgebra A B H
  let _ := isSeparable_residueField_fixedPoints_subalgebra A B G
  Algebra.isSeparable_tower_bot_of_isSeparable
    (IsLocalRing.ResidueField (FixedPoints.subalgebra A B G))
    (IsLocalRing.ResidueField (FixedPoints.subalgebra A B H)) (IsLocalRing.ResidueField B)

end TauCeti
