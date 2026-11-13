/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import TauCeti.RingTheory.AdicCompletion.Finite
public import TauCeti.RingTheory.Henselian.Integral

/-!
# Completeness of integral closures

The integral closure of a complete integrally closed Noetherian local domain in a finite
separable extension of its fraction field is complete at its own maximal ideal. No dimension-one
hypothesis, finiteness or perfection of the residue field, or normality of the field extension
is needed. In particular, this supplies completeness for the integral closures of complete DVRs.

Mathlib's `IsIntegralClosure.finite` supplies module-finiteness. Locality follows from
`TauCeti.IsIntegralClosure.isLocalRing` over the henselian base, and completeness then passes
to the finite local algebra by `IsAdicComplete.of_finite_of_isLocalRing`.

## Main results

* `TauCeti.IsIntegralClosure.isAdicComplete`: completeness for any local model of the integral
  closure and any chosen fraction field.
* `TauCeti.integralClosure.isAdicComplete`: completeness for `integralClosure A L` and any chosen
  fraction field.
* `TauCeti.integralClosure.isAdicComplete_fractionRing`: the instance using `FractionRing A`,
  as in Mathlib's integral-closure instances.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §2, Proposition 3, for complete DVRs.
-/

public section

namespace TauCeti

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

/-- The integral closure of a complete integrally closed Noetherian local domain in a finite
separable extension of a chosen fraction field is complete at its own maximal ideal. This is not
an instance because `K` cannot be inferred; see `integralClosure.isAdicComplete_fractionRing` for
the instance using `FractionRing A`. -/
theorem integralClosure.isAdicComplete (A K L : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure A L)) (integralClosure A L) :=
  IsIntegralClosure.isAdicComplete A K L _

/-- The integral closure of a complete integrally closed Noetherian local domain in a finite
separable extension of `FractionRing A` is complete at its own maximal ideal. -/
instance integralClosure.isAdicComplete_fractionRing (A L : Type*) [CommRing A] [IsDomain A]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Algebra.IsSeparable (FractionRing A) L] :
    IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure A L)) (integralClosure A L) :=
  integralClosure.isAdicComplete A (FractionRing A) L

end TauCeti
