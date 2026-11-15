/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Fixed-point submonoids, subrings, and subalgebras of local rings

Because two-sided inverses in a monoid `B` are unique, a multiplicative action of `G` on `B` fixes
the inverse of any `G`-fixed unit, so inclusion from `FixedPoints.submonoid G B`,
`FixedPoints.subring B G`, or `FixedPoints.subalgebra A B G` into `B` reflects and preserves units
(`isUnit_coe_fixedPoints_submonoid_iff`, `isUnit_coe_fixedPoints_subring_iff`,
`isUnit_coe_fixedPoints_subalgebra_iff`). When `B` is local, `FixedPoints.subring B G` and
`FixedPoints.subalgebra A B G` are local, with local inclusions into `B` and (when `algebraMap A B`
is local) a local structure map from `A`.
-/

public section

namespace TauCeti

/-- If `g` fixes a unit `u : Bˣ` under a multiplicative action, `g` also fixes `u⁻¹`. -/
theorem smul_val_inv_eq_of_smul_eq {B G : Type*} [Monoid B] [Monoid G] [MulDistribMulAction G B]
    {u : Bˣ} {g : G} (hu : g • (u : B) = u) : g • (↑u⁻¹ : B) = ↑u⁻¹ := by
  have hmul : g • (↑u⁻¹ : B) * (u : B) = 1 := by rw [← hu, ← smul_mul', Units.inv_mul, smul_one]
  rw [← mul_one (g • (↑u⁻¹ : B)), ← Units.mul_inv u, ← mul_assoc, hmul, one_mul]

/-- Inclusion `FixedPoints.submonoid G B →* B` reflects and preserves units. -/
@[simp] theorem isUnit_coe_fixedPoints_submonoid_iff {B G : Type*} [Monoid B] [Monoid G]
    [MulDistribMulAction G B] {x : FixedPoints.submonoid G B} : IsUnit (x : B) ↔ IsUnit x :=
  ⟨fun ⟨u, hu⟩ ↦ ⟨⟨x, ⟨↑u⁻¹, fun g ↦ smul_val_inv_eq_of_smul_eq (hu ▸ x.2 g)⟩,
    Subtype.ext (by simp [← hu]), Subtype.ext (by simp [← hu])⟩, rfl⟩,
   fun hx ↦ hx.map (FixedPoints.submonoid G B).subtype⟩

instance instIsLocalHomSubtypeFixedPointsSubmonoid {B G : Type*} [Monoid B] [Monoid G]
    [MulDistribMulAction G B] : IsLocalHom (FixedPoints.submonoid G B).subtype :=
  ⟨fun _ ↦ isUnit_coe_fixedPoints_submonoid_iff.mp⟩

/-- Inclusion `FixedPoints.subring B G →+* B` reflects and preserves units. -/
@[simp] theorem isUnit_coe_fixedPoints_subring_iff {B G : Type*} [Ring B] [Monoid G]
    [MulSemiringAction G B] {x : FixedPoints.subring B G} : IsUnit (x : B) ↔ IsUnit x :=
  ⟨fun hx ↦ ((isUnit_coe_fixedPoints_submonoid_iff (x := ⟨x.1, x.2⟩)).mp hx).map
    (⟨⟨fun z ↦ ⟨z.1, z.2⟩, rfl⟩, fun _ _ ↦ rfl⟩ : _ →* FixedPoints.subring B G),
   fun hx ↦ hx.map (FixedPoints.subring B G).subtype⟩

instance instIsLocalHomSubtypeFixedPointsSubring {B G : Type*} [Ring B] [Monoid G]
    [MulSemiringAction G B] : IsLocalHom (FixedPoints.subring B G).subtype :=
  ⟨fun _ ↦ isUnit_coe_fixedPoints_subring_iff.mp⟩

/-- Inclusion `FixedPoints.subalgebra A B G →ₐ[A] B` reflects and preserves units. -/
@[simp] theorem isUnit_coe_fixedPoints_subalgebra_iff {A B G : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    {x : FixedPoints.subalgebra A B G} : IsUnit (x : B) ↔ IsUnit x :=
  ⟨fun hx ↦ ((isUnit_coe_fixedPoints_submonoid_iff (x := ⟨x.1, x.2⟩)).mp hx).map
    (⟨⟨fun z ↦ ⟨z.1, z.2⟩, rfl⟩, fun _ _ ↦ rfl⟩ : _ →* FixedPoints.subalgebra A B G),
   fun hx ↦ hx.map (FixedPoints.subalgebra A B G).val⟩

instance instIsLocalHomValFixedPointsSubalgebra {A B G : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalHom (FixedPoints.subalgebra A B G).val :=
  ⟨fun _ ↦ isUnit_coe_fixedPoints_subalgebra_iff.mp⟩

instance instIsLocalHomAlgebraMapFixedPointsSubalgebra {A B G : Type*} [CommSemiring A]
    [CommSemiring B] [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalHom (algebraMap (FixedPoints.subalgebra A B G) B) :=
  ⟨fun _ ↦ isUnit_coe_fixedPoints_subalgebra_iff.mp⟩

instance instIsLocalHomAlgebraMapToFixedPointsSubalgebra {A B G : Type*} [CommSemiring A]
    [CommSemiring B] [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    [h : IsLocalHom (algebraMap A B)] :
    IsLocalHom (algebraMap A (FixedPoints.subalgebra A B G)) := by
  rw [IsScalarTower.algebraMap_eq A (FixedPoints.subalgebra A B G) B] at h
  exact isLocalHom_of_comp _ (algebraMap (FixedPoints.subalgebra A B G) B)

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
