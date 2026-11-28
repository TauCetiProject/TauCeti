/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import TauCeti.Algebra.Ring.Action.Invariant
import TauCeti.Algebra.Group.Action.MulDistribMulAction

/-!
# Fixed-point submonoids, subrings, and subalgebras of local rings

Unit reflection (`isUnit_coe_fixedPoints_*_iff`) makes inclusions from `FixedPoints.submonoid`,
`FixedPoints.subring`, and `FixedPoints.subalgebra` into `B` `IsLocalHom`, transferring
`IsLocalRing` from `B` to `FixedPoints.subring B G` and `FixedPoints.subalgebra A B G`.
For a submonoid-like subobject `H` of `G`, the inclusion `B^G → B^H` is also a local homomorphism
(`isLocalHom_algebraMap_fixedPoints_subalgebra`).
-/

public section
namespace TauCeti
variable {B G : Type*} [Monoid G]

instance instIsLocalHomSubtypeFixedPointsSubmonoid [Monoid B] [MulDistribMulAction G B] :
    IsLocalHom (FixedPoints.submonoid G B).subtype :=
  ⟨fun _ ↦ isUnit_coe_fixedPoints_submonoid_iff.mp⟩
instance instIsLocalHomSubtypeFixedPointsSubring [Ring B] [MulSemiringAction G B] :
    IsLocalHom (FixedPoints.subring B G).subtype :=
  ⟨fun _ ↦ isUnit_coe_fixedPoints_subring_iff.mp⟩
/-- The fixed-point subring of a local ring under any monoid action is a local ring. -/
instance instIsLocalRingFixedPointsSubring [Ring B] [IsLocalRing B] [MulSemiringAction G B] :
    IsLocalRing (FixedPoints.subring B G) :=
  RingHom.domain_isLocalRing (FixedPoints.subring B G).subtype

section Subalgebra
variable {A : Type*} [CommSemiring A]
instance instIsLocalHomAlgebraMapFixedPointsSubalgebra [CommSemiring B] [Algebra A B]
    [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalHom (algebraMap (FixedPoints.subalgebra A B G) B) :=
  ⟨fun _ ↦ isUnit_coe_fixedPoints_subalgebra_iff.mp⟩

/-- The fixed-point subalgebra of a local ring under any monoid action is a local ring. -/
instance FixedPoints.isLocalRing_subalgebra [CommSemiring B] [IsLocalRing B] [Algebra A B]
    [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalRing (FixedPoints.subalgebra A B G) :=
  RingHom.domain_isLocalRing (algebraMap (FixedPoints.subalgebra A B G) B)

/-- For any submonoid-like subobject `H` of `G`, the inclusion `B^G → B^H` is a local
homomorphism. -/
theorem isLocalHom_algebraMap_fixedPoints_subalgebra (A B : Type*) {G S : Type*} [CommSemiring A]
    [CommSemiring B] [Algebra A B] [Monoid G] [MulSemiringAction G B]
    [SMulCommClass G A B] [SetLike S G] [SubmonoidClass S G] (H : S) :
    letI := fixedPointsSubalgebraAlgebra A B H
    IsLocalHom (algebraMap (FixedPoints.subalgebra A B G) (FixedPoints.subalgebra A B H)) := by
  let _ := fixedPointsSubalgebraAlgebra A B H
  let _ := isScalarTower_fixedPoints_subalgebra A B H
  have : IsLocalHom ((algebraMap (FixedPoints.subalgebra A B H) B).comp
      (algebraMap (FixedPoints.subalgebra A B G) (FixedPoints.subalgebra A B H))) :=
    IsScalarTower.algebraMap_eq (FixedPoints.subalgebra A B G)
      (FixedPoints.subalgebra A B H) B ▸ inferInstance
  exact isLocalHom_of_comp _ (algebraMap (FixedPoints.subalgebra A B H) B)

end Subalgebra
end TauCeti
