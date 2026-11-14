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

Let a monoid `G` act multiplicatively on a monoid `B`. Because two-sided inverses in `B` are unique,
the inverse in `B` of a `G`-fixed unit is `G`-fixed, so inclusion from `FixedPoints.submonoid G B`,
`FixedPoints.subring B G`, or `FixedPoints.subalgebra A B G` into `B` reflects and preserves units
(`isUnit_coe_fixedPoints_submonoid_iff`, `isUnit_coe_fixedPoints_subring_iff`,
`isUnit_coe_fixedPoints_subalgebra_iff`). Consequently, when `B` is a local ring or semiring,
`FixedPoints.subring B G` and `FixedPoints.subalgebra A B G` are local, with local inclusions into
`B` and (when `algebraMap A B` is local) a local structure map from `A`.
-/

public section

namespace TauCeti

section Units

/-- If `g` fixes a unit `u : Bˣ` under a multiplicative action, `g` also fixes `u⁻¹`. -/
theorem smul_val_inv_eq_of_smul_eq {B G : Type*} [Monoid B] [Monoid G] [MulDistribMulAction G B]
    {u : Bˣ} {g : G} (hu : g • (u : B) = u) : g • (↑u⁻¹ : B) = ↑u⁻¹ := by
  have hmul : g • (↑u⁻¹ : B) * (u : B) = 1 := by rw [← hu, ← smul_mul', Units.inv_mul, smul_one]
  calc g • (↑u⁻¹ : B) = g • (↑u⁻¹ : B) * ((u : B) * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = (g • (↑u⁻¹ : B) * (u : B)) * ↑u⁻¹ := (mul_assoc _ _ _).symm
    _ = ↑u⁻¹ := by rw [hmul, one_mul]

/-- Inclusion `FixedPoints.submonoid G B →* B` reflects and preserves units. -/
@[simp]
theorem isUnit_coe_fixedPoints_submonoid_iff {B G : Type*} [Monoid B] [Monoid G]
    [MulDistribMulAction G B] {x : FixedPoints.submonoid G B} : IsUnit (x : B) ↔ IsUnit x :=
  ⟨fun ⟨u, hu⟩ ↦ ⟨⟨x, ⟨↑u⁻¹, fun g ↦ smul_val_inv_eq_of_smul_eq (hu ▸ x.2 g)⟩,
    Subtype.ext (by simp [← hu]), Subtype.ext (by simp [← hu])⟩, rfl⟩,
   fun hx ↦ hx.map (FixedPoints.submonoid G B).subtype⟩

/-- Inclusion `FixedPoints.subring B G →+* B` reflects and preserves units. -/
@[simp]
theorem isUnit_coe_fixedPoints_subring_iff {B G : Type*} [Ring B] [Monoid G]
    [MulSemiringAction G B] {x : FixedPoints.subring B G} : IsUnit (x : B) ↔ IsUnit x :=
  ⟨fun hx ↦ ((isUnit_coe_fixedPoints_submonoid_iff (x := ⟨x.1, x.2⟩)).mp hx).map
    (⟨⟨fun z ↦ ⟨z.1, z.2⟩, rfl⟩, fun _ _ ↦ rfl⟩ :
      FixedPoints.submonoid G B →* FixedPoints.subring B G),
   fun hx ↦ hx.map (FixedPoints.subring B G).subtype⟩

/-- The inclusion `FixedPoints.subring B G →+* B` is a local ring homomorphism. -/
instance instIsLocalHomSubtypeFixedPointsSubring {B G : Type*} [Ring B] [Monoid G]
    [MulSemiringAction G B] : IsLocalHom (FixedPoints.subring B G).subtype where
  map_nonunit _ hx := isUnit_coe_fixedPoints_subring_iff.mp hx

/-- Inclusion `FixedPoints.subalgebra A B G →ₐ[A] B` reflects and preserves units. -/
@[simp]
theorem isUnit_coe_fixedPoints_subalgebra_iff {A B G : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    {x : FixedPoints.subalgebra A B G} : IsUnit (x : B) ↔ IsUnit x :=
  ⟨fun hx ↦ ((isUnit_coe_fixedPoints_submonoid_iff (x := ⟨x.1, x.2⟩)).mp hx).map
    (⟨⟨fun z ↦ ⟨z.1, z.2⟩, rfl⟩, fun _ _ ↦ rfl⟩ :
      FixedPoints.submonoid G B →* FixedPoints.subalgebra A B G),
   fun hx ↦ hx.map (FixedPoints.subalgebra A B G).val.toRingHom⟩

/-- The inclusion `(FixedPoints.subalgebra A B G).val.toRingHom` into `B` is local. -/
instance instIsLocalHomValFixedPointsSubalgebra {A B G : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalHom (FixedPoints.subalgebra A B G).val.toRingHom where
  map_nonunit _ hx := isUnit_coe_fixedPoints_subalgebra_iff.mp hx

/-- The structure map `algebraMap (FixedPoints.subalgebra A B G) B` is local. -/
instance instIsLocalHomAlgebraMapFixedPointsSubalgebra {A B G : Type*} [CommSemiring A]
    [CommSemiring B] [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalHom (algebraMap (FixedPoints.subalgebra A B G) B) where
  map_nonunit _ hx := isUnit_coe_fixedPoints_subalgebra_iff.mp hx

/-- If `algebraMap A B` is local, so is `algebraMap A (FixedPoints.subalgebra A B G)`. -/
instance instIsLocalHomAlgebraMapToFixedPointsSubalgebra {A B G : Type*} [CommSemiring A]
    [CommSemiring B] [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    [h : IsLocalHom (algebraMap A B)] :
    IsLocalHom (algebraMap A (FixedPoints.subalgebra A B G)) := by
  rw [IsScalarTower.algebraMap_eq A (FixedPoints.subalgebra A B G) B] at h
  exact isLocalHom_of_comp _ (algebraMap (FixedPoints.subalgebra A B G) B)

end Units

section IsLocalRing

/-- The fixed-point subring of a local ring under a monoid action is a local ring. -/
instance instIsLocalRingFixedPointsSubring {B G : Type*} [Ring B] [IsLocalRing B] [Monoid G]
    [MulSemiringAction G B] : IsLocalRing (FixedPoints.subring B G) :=
  RingHom.domain_isLocalRing (FixedPoints.subring B G).subtype

/-- The fixed-point subalgebra of a local semiring under a monoid action is local. -/
instance instIsLocalRingFixedPointsSubalgebra {A B G : Type*} [CommSemiring A] [Semiring B]
    [IsLocalRing B] [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    IsLocalRing (FixedPoints.subalgebra A B G) :=
  RingHom.domain_isLocalRing (FixedPoints.subalgebra A B G).val.toRingHom

end IsLocalRing

end TauCeti
