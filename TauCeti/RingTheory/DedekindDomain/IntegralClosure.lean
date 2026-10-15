/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Proof-only: Krull–Akizuki supplies the Noetherian half, and is not named in any statement.
import TauCeti.RingTheory.IntegralClosure.NormalizationFinite
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.Integral

/-!
# Integral closures of one-dimensional Noetherian domains

Let `A` be a Noetherian domain of dimension at most one with fraction field `K`, and let `L` be a
finite extension of `K`. Any integral closure of `A` in `L` is a Dedekind domain. Neither integral
closedness of `A` nor separability of `L / K` is required. In particular, this applies to the
normalization of a singular affine curve and to inseparable function-field extensions.

## Main results

* `TauCeti.IsIntegralClosure.isDedekindDomain`: the result for any ring `C` known to be an integral
  closure of `A` in `L`.
* `TauCeti.integralClosure.isDedekindDomain`: the result for Mathlib's `integralClosure A L`, with
  a fraction field chosen by the caller.
* `TauCeti.integralClosure.isDedekindDomain_fractionRing`: the instance with `K := FractionRing A`.

The abstract form applies, for example, to a subring of a function field known to be an integral
closure. The ring `C` need not be assumed to be a domain: its map into the field `L` is injective.

Krull–Akizuki gives Noetherianity without separability, but does not assert that the integral
closure is a finite `A`-module. That stronger conclusion requires additional hypotheses on the
base ring or extension. For example, Mathlib proves module finiteness for separable extensions
when `A` is integrally closed, and `TauCeti.IsIntegralClosure.finite_adjoin_of_transcendental`
proves it over a polynomial subalgebra of a function field without separability.

## References

The proof follows Mathlib's `IsIntegralClosure.isDedekindDomain`
(`Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean`), replacing its separable Noetherianity
argument with Krull–Akizuki, `TauCeti.IsIntegralClosure.isNoetherianRing`.
-/

public section

namespace TauCeti

/-- An integral closure of a Noetherian domain of dimension at most one in a finite extension
of its fraction field is a Dedekind domain. Neither integral closedness of the base ring nor
separability of the extension is required. The integral closure need not be assumed to be a domain.

This does not assert finiteness as a module over the base ring. -/
theorem IsIntegralClosure.isDedekindDomain (A : Type*) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Ring.DimensionLEOne A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type*) [Field L] [Algebra A L]
    [Algebra K L] [IsScalarTower A K L] [Module.Finite K L] (C : Type*) [CommRing C]
    [Algebra A C] [Algebra C L] [IsScalarTower A C L] [IsIntegralClosure C A L] :
    IsDedekindDomain C :=
  have : IsDomain C := Function.Injective.isDomain (algebraMap C L)
    (IsIntegralClosure.algebraMap_injective C A L)
  have : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  have : Algebra.IsIntegral A C := IsIntegralClosure.isIntegral_algebra A L
  { _root_.TauCeti.IsIntegralClosure.isNoetherianRing (A := A) (L := L) K C,
    Ring.DimensionLEOne.of_isIntegral A C,
    (isIntegrallyClosed_iff L).mpr fun {x} hx =>
      ⟨IsIntegralClosure.mk' C x (isIntegral_trans (R := A) _ hx),
        IsIntegralClosure.algebraMap_mk' _ _ _⟩ with : IsDedekindDomain C }

/-- The integral closure of a Noetherian domain of dimension at most one in a finite extension
of its fraction field is a Dedekind domain, with no separability hypothesis.

This cannot be an instance since `K` cannot be inferred; see
`integralClosure.isDedekindDomain_fractionRing` for the instance with `K := FractionRing A`. -/
theorem integralClosure.isDedekindDomain (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.DimensionLEOne A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type*) [Field L] [Algebra A L]
    [Algebra K L] [IsScalarTower A K L] [Module.Finite K L] :
    IsDedekindDomain (integralClosure A L) :=
  IsIntegralClosure.isDedekindDomain A K L (integralClosure A L)

/-- For a Noetherian domain `A` of dimension at most one and a finite extension `L` of
`FractionRing A`, the integral closure of `A` in `L` is a Dedekind domain. No separability is
required. See `integralClosure.isDedekindDomain` to choose the fraction field. -/
instance integralClosure.isDedekindDomain_fractionRing {A : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Ring.DimensionLEOne A] {L : Type*} [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [Module.Finite (FractionRing A) L] :
    IsDedekindDomain (integralClosure A L) :=
  integralClosure.isDedekindDomain A (FractionRing A) L

end TauCeti
