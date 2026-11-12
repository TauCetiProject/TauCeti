/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import TauCeti.RingTheory.AdicCompletion.Finite
public import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
public import TauCeti.RingTheory.Henselian.Integral
import TauCeti.RingTheory.DedekindDomain.IntegralClosure

/-!
# Integral closures of henselian discrete valuation rings

The integral closure of a henselian DVR in a finite extension of its fraction field is again
a DVR, without a separability assumption. For finite separable extensions, completeness of the
base DVR implies completeness of its integral closure at its own maximal ideal. No finiteness
or perfection of the residue field, and no normality of the field extension, is needed.

These results provide integer rings for ramification theory over complete discretely valued
fields with arbitrary residue fields. Finiteness, freeness and rank are already supplied by
Mathlib's `IsIntegralClosure.finite`, `IsIntegralClosure.module_free` and
`IsIntegralClosure.rank`; the additional step here is locality. A domain integral over a
henselian local ring is local, and a local Dedekind domain that is not a field is a DVR.
Krull–Akizuki supplies Dedekindness even without separability. Completeness passes to finite
local algebras, also over integrally closed Noetherian local bases that are not DVRs.

`TauCeti.IsIntegralClosure.isDiscreteValuationRing` and
`TauCeti.IsIntegralClosure.isAdicComplete` allow any model of the integral closure and any chosen
fraction field. Instances for `integralClosure A L` use `FractionRing A`, as do Mathlib's
integral-closure instances.

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
  have := isLocalRing_of_isDomain_of_isIntegral_of_henselianRing A B
  apply IsDiscreteValuationRing.of_krullDimLE_one
  intro hB
  exact IsDiscreteValuationRing.not_isField A
    (isField_of_isIntegral_of_isField (algebraMap_injective_of_field_isFractionRing A B K L) hB)

/-- A local integral closure of a complete integrally closed Noetherian local domain in a
finite separable extension of its fraction field is complete at its own maximal ideal. -/
theorem IsIntegralClosure.isAdicComplete
    (A K L B : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L]
    [CommRing B] [IsLocalRing B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] : IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
  have := _root_.IsIntegralClosure.finite A K L B
  exact _root_.IsAdicComplete.of_finite_of_isLocalRing A B

namespace integralClosure

variable (A L : Type*) [CommRing A] [IsDomain A]
  [Field L] [Algebra A L] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]

/-- The integral closure of a henselian DVR in a finite field extension is a DVR, without a
separability assumption. -/
instance isDiscreteValuationRing [IsDiscreteValuationRing A]
    [HenselianRing A (IsLocalRing.maximalIdeal A)] :
    IsDiscreteValuationRing (integralClosure A L) :=
  IsIntegralClosure.isDiscreteValuationRing A (FractionRing A) L _

/-- The integral closure of a complete integrally closed Noetherian local domain in a finite
separable field extension is complete at its own maximal ideal. -/
instance isAdicComplete [IsIntegrallyClosed A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Algebra.IsSeparable (FractionRing A) L] :
    IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure A L)) (integralClosure A L) :=
  IsIntegralClosure.isAdicComplete A (FractionRing A) L _

end integralClosure

end TauCeti
