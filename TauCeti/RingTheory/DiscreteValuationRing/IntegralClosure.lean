/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import TauCeti.RingTheory.AdicCompletion.Finite
public import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
public import TauCeti.RingTheory.Henselian.Basic
public import TauCeti.RingTheory.Henselian.Integral

/-!
# Integral closures of henselian discrete valuation rings

The integral closure of a henselian DVR in a finite separable extension of its fraction field is
again a DVR. If the base DVR is complete, its integral closure is complete at its own maximal
ideal. No finiteness or perfection of the residue field, and no normality of the field extension,
is needed.

These results provide integer rings for ramification theory over complete discretely valued
fields with arbitrary residue fields. Finiteness, freeness and rank are already supplied by
Mathlib's `IsIntegralClosure.finite`, `IsIntegralClosure.module_free` and
`IsIntegralClosure.rank`; the additional step here is locality. A finite domain over a henselian
local ring is local, and a local Dedekind domain that is not a field is a DVR. Completeness then
passes to the finite local algebra.

The general theorem allows any model of the integral closure and any chosen fraction field.
Instances for `integralClosure A L` use `FractionRing A`, as do Mathlib's integral-closure
instances.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §2, Proposition 3.
-/

public section

namespace TauCeti

/-- The integral closure of a henselian DVR in a finite separable extension of its fraction
field is a DVR. The integral closure may be any ring satisfying `IsIntegralClosure`. -/
theorem isDiscreteValuationRing_of_isIntegralClosure
    (A K L B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [HenselianLocalRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] : IsDiscreteValuationRing B := by
  have := IsIntegralClosure.finite A K L B
  have := IsIntegralClosure.isDedekindDomain A K L B
  have := IsIntegralClosure.isIntegral_algebra A L (A := B)
  have : Module.IsTorsionFree A L := .trans_faithfulSMul A K L
  have := IsIntegralClosure.isTorsionFree A L (A := B)
  have := isLocalRing_of_finite_of_henselianRing A B
  apply IsDiscreteValuationRing.of_krullDimLE_one
  intro hB
  exact IsDiscreteValuationRing.not_isField A
    (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective A B) hB)

end TauCeti

namespace integralClosure

variable (A L : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field L] [Algebra A L] [Algebra (FractionRing A) L]
  [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
  [Algebra.IsSeparable (FractionRing A) L]

/-- The integral closure of a henselian DVR in a finite separable field extension is a DVR. -/
instance isDiscreteValuationRing [HenselianLocalRing A] :
    IsDiscreteValuationRing (integralClosure A L) :=
  TauCeti.isDiscreteValuationRing_of_isIntegralClosure A (FractionRing A) L _

/-- The integral closure of a complete DVR in a finite separable field extension is complete
for its maximal ideal, not merely for the ideal extended from the base. -/
instance isAdicComplete [IsAdicComplete (IsLocalRing.maximalIdeal A) A] :
    IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure A L)) (integralClosure A L) := by
  have := IsIntegralClosure.finite A (FractionRing A) L (integralClosure A L)
  exact IsAdicComplete.of_finite_of_isLocalRing A _

end integralClosure
