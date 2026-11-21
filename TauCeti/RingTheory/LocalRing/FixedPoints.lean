/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.MulDistribMulAction
public import TauCeti.Algebra.Ring.Action.Invariant
public import TauCeti.RingTheory.LocalRing.RingHom

/-!
# Fixed-point submonoids, subrings, and subalgebras of local rings

Unit reflection (`isUnit_coe_fixedPoints_*_iff`) makes inclusions from `FixedPoints.submonoid`,
`FixedPoints.subring`, and `FixedPoints.subalgebra` into `B` `IsLocalHom`, transferring
`IsLocalRing` from `B` to `FixedPoints.subring B G`.
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
instance instIsLocalHomValFixedPointsSubalgebra [Semiring B] [Algebra A B] [MulSemiringAction G B]
    [SMulCommClass G A B] : IsLocalHom (FixedPoints.subalgebra A B G).val :=
  ⟨fun _ ↦ isUnit_coe_fixedPoints_subalgebra_iff.mp⟩
end Subalgebra
end TauCeti
