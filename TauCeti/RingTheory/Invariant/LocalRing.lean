/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Invariant
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Local-ring structure on fixed-point subrings

Let a monoid `G` act on a semiring `B` by semiring endomorphisms (`MulSemiringAction G B`).
If a fixed element `x` is a unit of `B`, its two-sided inverse is also fixed by `G`, by uniqueness
of inverses. Consequently the inclusion of the fixed subsemiring or fixed subring into `B` is a
local homomorphism (`IsLocalHom`), and whenever `B` is a local ring, so are its fixed subsemiring
and fixed subring (the fixed subalgebra counterpart is in
`TauCeti/RingTheory/Invariant/Basic.lean`, and the discrete valuation ring counterpart is in
`TauCeti/RingTheory/DiscreteValuationRing/Invariant.lean`).

## Main results

* `TauCeti.FixedPoints.instIsLocalHomSubsemiringSubtype`,
  `TauCeti.FixedPoints.instIsLocalHomSubringSubtype`: inclusions of fixed-point subsemirings and
  subrings are local homomorphisms.
* `TauCeti.FixedPoints.instIsLocalRingSubsemiring`,
  `TauCeti.FixedPoints.instIsLocalRingSubring`: fixed subsemirings and subrings in a local ring
  form a local ring.
-/

public section

namespace TauCeti.FixedPoints

section LocalRing

/-- The inclusion of the fixed subsemiring of a monoid action is a local homomorphism: if a fixed
element is a unit in the ambient semiring, its inverse is again fixed. -/
instance instIsLocalHomSubsemiringSubtype {B G : Type*} [Semiring B] [Monoid G]
    [MulSemiringAction G B] : IsLocalHom (FixedPoints.subsemiring B G).subtype where
  map_nonunit x hx := by
    obtain ⟨u, hu⟩ := hx
    have hinv : (↑u⁻¹ : B) ∈ FixedPoints.subsemiring B G := fun g ↦ by
      calc
        g • (↑u⁻¹ : B) = (g • (↑u⁻¹ : B)) * ((u : B) * (↑u⁻¹ : B)) := by
          rw [Units.mul_inv, mul_one]
        _ = (g • (↑u⁻¹ : B)) * (g • (u : B)) * (↑u⁻¹ : B) := by
          rw [← mul_assoc, hu, Subsemiring.coe_subtype, x.property g]
        _ = g • ((↑u⁻¹ : B) * (u : B)) * (↑u⁻¹ : B) := by
          rw [smul_mul']
        _ = (↑u⁻¹ : B) := by
          rw [Units.inv_mul, smul_one, one_mul]
    exact isUnit_iff_exists.2 ⟨⟨↑u⁻¹, hinv⟩,
      Subtype.ext (by simp [hu]), Subtype.ext (by simp [hu])⟩

/-- The inclusion of the fixed subring of a monoid action is a local homomorphism. -/
instance instIsLocalHomSubringSubtype {B G : Type*} [Ring B] [Monoid G]
    [MulSemiringAction G B] : IsLocalHom (FixedPoints.subring B G).subtype :=
  inferInstanceAs (IsLocalHom (FixedPoints.subsemiring B G).subtype)

/-- The fixed subsemiring of a monoid action on a local semiring is local. -/
instance instIsLocalRingSubsemiring {B G : Type*} [Semiring B] [IsLocalRing B] [Monoid G]
    [MulSemiringAction G B] : IsLocalRing (FixedPoints.subsemiring B G) :=
  (FixedPoints.subsemiring B G).subtype.domain_isLocalRing

/-- The fixed subring of a monoid action on a local ring is local. -/
instance instIsLocalRingSubring {B G : Type*} [Ring B] [IsLocalRing B] [Monoid G]
    [MulSemiringAction G B] : IsLocalRing (FixedPoints.subring B G) :=
  (FixedPoints.subring B G).subtype.domain_isLocalRing

end LocalRing

end TauCeti.FixedPoints
