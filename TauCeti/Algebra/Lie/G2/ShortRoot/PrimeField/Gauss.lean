/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Gauss
public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor

/-!
# Short-root Gauss factorization in the characteristic-three G₂ carrier

The opposite short simple-root points satisfy the integral rank-one Gauss relation in the
subgroup scheme generated over `𝔽₃`. The lower–torus–upper parameters are uniquely determined:
the torus parameter must be the unit `1 + ab`, and the two root parameters are `b/(1+ab)` and
`a/(1+ab)`. No field or reducedness hypothesis on the value algebra is required.

Transfer uses the existing equalities of the root and torus matrices, not an identification of
the prime-field generated carrier with the reduction of the integral toral closure. Neither
carrier is identified here with an independently pinned simply connected group scheme; the
identities transfer to that group only along an identification respecting the root and torus
maps.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

universe v

namespace TauCeti.G2ShortRoot.PrimeField

variable {A : Type v} [CommRing A] [Algebra (ZMod 3) A]

/-- The complete characterization of a short-root Gauss factorization in the carrier generated
over `𝔽₃`. The factorization forces invertibility of `1 + ab` and fixes every parameter. -/
@[simp↓]
theorem rootSubgroupPoints_inl_zero_mul_inr_zero_eq_iff (a b c d : A) (u : Aˣ) :
    rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr 0) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr 0) A (Multiplicative.ofAdd c) *
        weightTorusPoints A (Pi.mulSingle 0 u) *
        rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd d) ↔
      (u : A) = 1 + a * b ∧ c = b * ↑(u⁻¹) ∧ d = a * ↑(u⁻¹) := by
  -- Both point groups embed into the same GL₇; the root and torus matrices agree there.
  rw [← Subtype.coe_inj]
  simp only [Subgroup.coe_mul, coe_rootSubgroupPoints, coe_weightTorusPoints]
  simpa only [← Subgroup.coe_mul, Subtype.coe_inj] using
    (IntegralToralClosure.rootSubgroupPoints_inl_zero_mul_inr_zero_eq_iff a b c d u)

/-- **Gauss factorization for the short simple root over `𝔽₃`.** This is an identity in the
actual generated carrier over every commutative value algebra, including nonreduced algebras. -/
theorem rootSubgroupPoints_inl_zero_mul_inr_zero (a b : A) (u : Aˣ)
    (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints (.inr 0) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints (.inr 0) A (Multiplicative.ofAdd (b * ↑(u⁻¹))) *
        weightTorusPoints A (Pi.mulSingle 0 u) *
        rootSubgroupPoints (.inl 0) A (Multiplicative.ofAdd (a * ↑(u⁻¹))) :=
  (rootSubgroupPoints_inl_zero_mul_inr_zero_eq_iff a b _ _ u).2 ⟨hu, rfl, rfl⟩

end TauCeti.G2ShortRoot.PrimeField
