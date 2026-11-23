/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
public import TauCeti.RingTheory.Henselian.Integral
import TauCeti.RingTheory.DedekindDomain.IntegralClosure

/-!
# Integral closures of henselian discrete valuation rings

The integral closure of a henselian DVR in a finite extension of its fraction field is again
a DVR, without a separability assumption. No finiteness or perfection of the residue field,
and no normality of the field extension, is needed. Completeness of integral closures is treated
separately in `TauCeti/RingTheory/AdicCompletion/IntegralClosure.lean`.

These results provide integer rings for ramification theory over complete discretely valued
fields with arbitrary residue fields. When `L / K` is separable (`Algebra.IsSeparable K L`),
finiteness, freeness and rank are already supplied by Mathlib's `IsIntegralClosure.finite`,
`IsIntegralClosure.module_free` and `IsIntegralClosure.rank`; the additional step here is locality.
A domain integral over a henselian local ring is local, and a local Dedekind domain that is not a
field is a DVR.
Krull–Akizuki supplies Dedekindness even without separability.

`TauCeti.IsIntegralClosure.isDiscreteValuationRing` allows any model of the integral closure
and any chosen fraction field. `TauCeti.integralClosure.isDiscreteValuationRing` specializes to
`integralClosure A L`, still allowing a chosen fraction field. The instance
`TauCeti.integralClosure.isDiscreteValuationRing_fractionRing` uses `FractionRing A`, as do
Mathlib's integral-closure instances.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §2, Proposition 3.
-/

public section

namespace TauCeti

/-- The integral closure of a henselian DVR in a finite extension of its fraction field is a
DVR, without a separability assumption. The closure may be any model of `IsIntegralClosure`. -/
theorem IsIntegralClosure.isDiscreteValuationRing
    (A K L B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [HenselianRing A (IsLocalRing.maximalIdeal A)] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] : IsDiscreteValuationRing B := by
  have := IsIntegralClosure.isDedekindDomain A K L B
  have := _root_.IsIntegralClosure.isIntegral_algebra A L (A := B)
  have := IsIntegralClosure.isLocalRing A L B
  apply IsDiscreteValuationRing.of_krullDimLE_one
  intro hB
  exact IsDiscreteValuationRing.not_isField A
    (isField_of_isIntegral_of_isField (algebraMap_injective_of_field_isFractionRing A B K L) hB)

namespace integralClosure

/-- The integral closure of a henselian DVR in a finite extension of a chosen fraction field is
a DVR, without a separability assumption. This is not an instance because `K` cannot be inferred;
see `isDiscreteValuationRing_fractionRing` for the instance using `FractionRing A`. -/
theorem isDiscreteValuationRing (A K L : Type*) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [HenselianRing A (IsLocalRing.maximalIdeal A)]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L] [FiniteDimensional K L] :
    IsDiscreteValuationRing (integralClosure A L) :=
  IsIntegralClosure.isDiscreteValuationRing A K L _

variable (A L : Type*) [CommRing A] [IsDomain A]
  [Field L] [Algebra A L] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]

/-- The integral closure of a henselian DVR in a finite field extension is a DVR, without a
separability assumption. -/
instance isDiscreteValuationRing_fractionRing [IsDiscreteValuationRing A]
    [HenselianRing A (IsLocalRing.maximalIdeal A)] :
    IsDiscreteValuationRing (integralClosure A L) :=
  isDiscreteValuationRing A (FractionRing A) L

end integralClosure

end TauCeti
