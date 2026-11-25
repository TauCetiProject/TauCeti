/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IsGaloisGroup.Defs
public import TauCeti.RingTheory.DiscreteValuationRing.Invariant
public import TauCeti.RingTheory.LocalRing.RamificationGroup
public import TauCeti.RingTheory.RamificationInertia.DiscreteValuationRing
import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure
import TauCeti.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Inertia group cardinality on discrete valuation rings

For a faithful finite Galois action `G` on a discrete valuation ring `B` with invariant DVR `A`
and separable residue extension, `#G_0 = e(B / A)` (`natCard_ramificationGroup_zero`). More
generally, over any local ring `A` with separable residue extension, `#G_0 = e(B / B^G)`
(`natCard_ramificationGroup_zero_fixedPoints`). Neither completeness of `A` nor finiteness of its
residue field is assumed.

## Main results

* `TauCeti.IsLocalRing.natCard_ramificationGroup_zero`: `#G_0 = e(B / A)` for invariant DVR `A`.
* `TauCeti.IsLocalRing.natCard_ramificationGroup_zero_fixedPoints`: `#G_0 = e(B / B^G)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1, Proposition 3.
-/

public section

open IsLocalRing

namespace TauCeti

namespace IsLocalRing

/-- For a faithful finite Galois action `G` on a DVR `B` with invariant DVR `A` and separable
residue extension, `#G_0 = e(B / A)`. -/
theorem natCard_ramificationGroup_zero {A B G : Type*} [CommRing A] [IsDomain A]
    [_root_.IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [_root_.IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    Nat.card (ramificationGroup G B 0) = (maximalIdeal B).ramificationIdx A := by
  have _ : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have _ : FaithfulSMul A B := IsDiscreteValuationRing.faithfulSMul_of_isIntegral (R := A) (S := B)
  have _ : Module.Finite A B := IsGaloisGroup.moduleFinite_of_isIntegrallyClosed G A B
  let := Ideal.Quotient.field (maximalIdeal A)
  let := Ideal.Quotient.field (maximalIdeal B)
  have _ : Algebra.IsSeparable (A ⧸ maximalIdeal A) (B ⧸ maximalIdeal B) :=
    TauCeti.isSeparable_quotient_of_residueField A B
  rw [ramificationGroup_zero_eq_inertia,
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B) G]
  exact Ideal.card_inertia_eq_ramificationIdxIn_of_isSeparable (G := G)
    (maximalIdeal A) (maximalIdeal B)

/-- For a finite group `G` acting faithfully on a DVR `B` over a local ring `A` with separable
residue extension, `#G_0 = e(B / B^G)`. -/
theorem natCard_ramificationGroup_zero_fixedPoints
    (A B G : Type*) [CommRing A] [IsLocalRing A] [CommRing B] [IsDomain B]
    [_root_.IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] [Group G]
    [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [FaithfulSMul G B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    Nat.card (ramificationGroup G B 0) =
      (maximalIdeal B).ramificationIdx (FixedPoints.subalgebra A B G) :=
  let _ : IsGaloisGroup G (FixedPoints.subalgebra A B G) B :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have _ : Algebra.IsSeparable (ResidueField (FixedPoints.subalgebra A B G)) (ResidueField B) :=
    Algebra.isSeparable_tower_top_of_isSeparable (ResidueField A) _ (ResidueField B)
  natCard_ramificationGroup_zero

end IsLocalRing

end TauCeti
