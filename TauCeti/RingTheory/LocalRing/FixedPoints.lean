/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Fixed-point subrings and subalgebras of local rings

Let a group `G` act by ring automorphisms on a commutative ring `B`. Because two-sided inverses in
`B` are unique, the inverse in `B` of a `G`-fixed unit is itself `G`-fixed: an element of the
invariant subring `FixedPoints.subring B G` or invariant subalgebra `FixedPoints.subalgebra A B G`
is a unit there if and only if its image in `B` is a unit. No finiteness assumption on `G` and no
domain assumption on `B` is required.

When `B` is a local ring, this unit reflection makes `FixedPoints.subring B G` and
`FixedPoints.subalgebra A B G` local rings as well, with local inclusion maps into `B` and, for a
local base algebra `A → B`, a local structure map from `A`.

## Main results

* `TauCeti.isUnit_coe_fixedPoints_subring_iff`, `TauCeti.isUnit_coe_fixedPoints_subalgebra_iff`:
  inclusion from `FixedPoints.subring B G` or `FixedPoints.subalgebra A B G` into `B` reflects and
  preserves units.
* `TauCeti.instIsLocalHomSubtypeFixedPointsSubring`,
  `TauCeti.instIsLocalHomAlgebraMapFixedPointsSubalgebra`: the inclusions into `B` are local ring
  homomorphisms.
* `TauCeti.instIsLocalRingFixedPointsSubring`, `TauCeti.instIsLocalRingFixedPointsSubalgebra`:
  the fixed-point subring and subalgebra of a local ring under a group action are local rings.
* `TauCeti.instIsLocalHomAlgebraMapToFixedPointsSubalgebra`: if `algebraMap A B` is local, so is
  `algebraMap A (FixedPoints.subalgebra A B G)`.
-/

public section

namespace TauCeti

section CommRing

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B]

/-- If an element of `B` fixed by a group `G` is a unit in `B`, its inverse in `B` is also fixed by
`G`. -/
theorem smul_val_inv_eq_of_smul_eq {u : Bˣ} (hu : ∀ g : G, g • (u : B) = u) (g : G) :
    g • (↑u⁻¹ : B) = ↑u⁻¹ := by
  have hmul : g • (↑u⁻¹ : B) * (u : B) = 1 := by
    rw [← hu g, ← smul_mul', Units.inv_mul, smul_one]
  calc
    g • (↑u⁻¹ : B) = g • (↑u⁻¹ : B) * ((u : B) * ↑u⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = (g • (↑u⁻¹ : B) * (u : B)) * ↑u⁻¹ := (mul_assoc _ _ _).symm
    _ = ↑u⁻¹ := by rw [hmul, one_mul]

/-- An element of `FixedPoints.subring B G` is a unit in `B` if and only if it is a unit in the
fixed-point subring. -/
@[simp]
theorem isUnit_coe_fixedPoints_subring_iff {x : FixedPoints.subring B G} :
    IsUnit (x : B) ↔ IsUnit x := by
  refine ⟨?_, fun hx ↦ hx.map (FixedPoints.subring B G).subtype⟩
  rintro ⟨u, hu⟩
  have hfix : ∀ g : G, g • (u : B) = u := fun g ↦ by rw [hu, x.2 g]
  refine ⟨⟨x, ⟨↑u⁻¹, smul_val_inv_eq_of_smul_eq hfix⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (by simp [← hu])
  · exact Subtype.ext (by simp [← hu])

/-- The inclusion `FixedPoints.subring B G →+* B` is a local ring homomorphism. -/
instance instIsLocalHomSubtypeFixedPointsSubring :
    IsLocalHom (FixedPoints.subring B G).subtype where
  map_nonunit _ hx := isUnit_coe_fixedPoints_subring_iff.mp hx

/-- An element of `FixedPoints.subalgebra A B G` is a unit in `B` if and only if it is a unit in
the fixed-point subalgebra. -/
@[simp]
theorem isUnit_coe_fixedPoints_subalgebra_iff [SMulCommClass G A B]
    {x : FixedPoints.subalgebra A B G} :
    IsUnit (x : B) ↔ IsUnit x := by
  refine ⟨?_, fun hx ↦ hx.map (algebraMap (FixedPoints.subalgebra A B G) B)⟩
  rintro ⟨u, hu⟩
  have hfix : ∀ g : G, g • (u : B) = u := fun g ↦ by rw [hu, x.2 g]
  refine ⟨⟨x, ⟨↑u⁻¹, smul_val_inv_eq_of_smul_eq hfix⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (by simp [← hu])
  · exact Subtype.ext (by simp [← hu])

/-- The structure map `FixedPoints.subalgebra A B G →+* B` is a local ring homomorphism. -/
instance instIsLocalHomAlgebraMapFixedPointsSubalgebra [SMulCommClass G A B] :
    IsLocalHom (algebraMap (FixedPoints.subalgebra A B G) B) where
  map_nonunit _ hx := isUnit_coe_fixedPoints_subalgebra_iff.mp hx

/-- If `algebraMap A B` is a local ring homomorphism, so is
`algebraMap A (FixedPoints.subalgebra A B G)`. -/
instance instIsLocalHomAlgebraMapToFixedPointsSubalgebra [SMulCommClass G A B]
    [h : IsLocalHom (algebraMap A B)] :
    IsLocalHom (algebraMap A (FixedPoints.subalgebra A B G)) := by
  rw [IsScalarTower.algebraMap_eq A (FixedPoints.subalgebra A B G) B] at h
  exact isLocalHom_of_comp _ (algebraMap (FixedPoints.subalgebra A B G) B)

end CommRing

section IsLocalRing

variable {A B G : Type*} [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
  [Group G] [MulSemiringAction G B]

/-- The fixed-point subring of a local ring under a group action is a local ring. -/
instance instIsLocalRingFixedPointsSubring : IsLocalRing (FixedPoints.subring B G) :=
  RingHom.domain_isLocalRing (FixedPoints.subring B G).subtype

/-- The fixed-point subalgebra of a local ring under a group action is a local ring. -/
instance instIsLocalRingFixedPointsSubalgebra [SMulCommClass G A B] :
    IsLocalRing (FixedPoints.subalgebra A B G) :=
  RingHom.domain_isLocalRing (algebraMap (FixedPoints.subalgebra A B G) B)

end IsLocalRing

end TauCeti
