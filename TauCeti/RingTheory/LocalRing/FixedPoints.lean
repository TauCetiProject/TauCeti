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

Using unit reflection of fixed-point inclusions (`isUnit_coe_fixedPoints_submonoid_iff`,
`isUnit_coe_fixedPoints_subring_iff`, `isUnit_coe_fixedPoints_subalgebra_iff`), the inclusions of
`FixedPoints.submonoid G B`, `FixedPoints.subring B G`, and `FixedPoints.subalgebra A B G` into
`B` are `IsLocalHom`. Consequently, when `B` is local, `FixedPoints.subring B G` and
`FixedPoints.subalgebra A B G` are local.
-/

public section

namespace TauCeti

instance instIsLocalHomSubtypeFixedPointsSubmonoid {B G : Type*} [Monoid B] [Monoid G]
    [MulDistribMulAction G B] : IsLocalHom (FixedPoints.submonoid G B).subtype :=
  ⟨fun _ ↦ isUnit_coe_fixedPoints_submonoid_iff.mp⟩
instance instIsLocalHomSubtypeFixedPointsSubring {B G : Type*} [Ring B] [Monoid G]
    [MulSemiringAction G B] : IsLocalHom (FixedPoints.subring B G).subtype :=
  ⟨fun _ ↦ isUnit_coe_fixedPoints_subring_iff.mp⟩
instance instIsLocalHomValFixedPointsSubalgebra {A B G : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalHom (FixedPoints.subalgebra A B G).val :=
  ⟨fun _ ↦ isUnit_coe_fixedPoints_subalgebra_iff.mp⟩
instance instIsLocalHomAlgebraMapFixedPointsSubalgebra {A B G : Type*} [CommSemiring A]
    [CommSemiring B] [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalHom (algebraMap (FixedPoints.subalgebra A B G) B) :=
  ⟨fun _ ↦ isUnit_coe_fixedPoints_subalgebra_iff.mp⟩

/-- The fixed-point subring of a local ring under any monoid action is a local ring. -/
instance instIsLocalRingFixedPointsSubring {B G : Type*} [Ring B] [IsLocalRing B] [Monoid G]
    [MulSemiringAction G B] : IsLocalRing (FixedPoints.subring B G) :=
  RingHom.domain_isLocalRing (FixedPoints.subring B G).subtype
/-- The fixed-point subalgebra of a local semiring under any monoid action is local. -/
instance instIsLocalRingFixedPointsSubalgebra {A B G : Type*} [CommSemiring A] [Semiring B]
    [IsLocalRing B] [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalRing (FixedPoints.subalgebra A B G) :=
  RingHom.domain_isLocalRing ((FixedPoints.subalgebra A B G).val : _ →+* B)

end TauCeti
