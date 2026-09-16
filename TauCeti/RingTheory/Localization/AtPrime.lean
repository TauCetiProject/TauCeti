/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# The localisation of a domain at a prime, inside an abstract fraction field

Let `R` be a domain with fraction field `K` and let `p` be a prime ideal of `R`. The localisation
`Localization.AtPrime p` embeds in `K`, and `K` is again its fraction field. Mathlib records this
only for `K = FractionRing R`: the instance `IsLocalization.instAlgebraLocalizationAtPrime`, and
the `IsScalarTower` and `IsFractionRing` instances beside it, all target
`Localization (nonZeroDivisors R)` on the nose. A statement about a Dedekind domain `O` and *some*
fraction field `K` — a number field `K` with `O = 𝓞 K`, say — cannot use them.

This file supplies the same three instances for an arbitrary fraction field `K`, from
`Ideal.primeCompl_le_nonZeroDivisors`, exactly as Mathlib builds the `FractionRing` case. For
`K = FractionRing R` the new `Algebra` instance is definitionally the existing one: both are
`IsLocalization.localizationAlgebraOfSubmonoidLe` for `p.primeCompl ≤ nonZeroDivisors R`, an
`abbrev`, and they differ only in the proof of that inequality.

## Main declarations

* `Localization.AtPrime.algebraOfIsFractionRing : Algebra (Localization.AtPrime p) K`, the lift of
  `algebraMap R K` along the localisation;
* `Localization.AtPrime.isScalarTower_of_isFractionRing : IsScalarTower R (Localization.AtPrime p)
  K`, saying that lift extends `algebraMap R K`;
* `Localization.AtPrime.isFractionRing : IsFractionRing (Localization.AtPrime p) K`.

They are global instances: the point of stating them once is that every consumer — first the
global minimal models of `TauCeti/AlgebraicGeometry/EllipticCurve/GlobalMinimalModel.lean`, where
the localisation is at a height-one prime of a Dedekind domain — finds them by instance search
rather than installing them locally at each use site. The `Algebra` instance carries data and is
`noncomputable`, as `IsLocalization.lift` is.

This is the domain-level part of the localisation instances asked for by
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 4.5a; the height-one-prime specialisation and its
valuation bound are in `TauCeti/RingTheory/DedekindDomain/LocalizationAtPrime.lean`.
-/

public section

namespace Localization.AtPrime

variable {R : Type*} [CommRing R] [IsDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (p : Ideal R) [p.IsPrime]

/-- The localisation of a domain `R` at a prime `p` maps to any fraction field `K` of `R`: the
`Algebra` structure lifting `algebraMap R K`, which inverts every element outside `p` because
those are nonzero. For `K = FractionRing R` this is definitionally Mathlib's
`IsLocalization.instAlgebraLocalizationAtPrime`. -/
noncomputable instance algebraOfIsFractionRing : Algebra (Localization.AtPrime p) K :=
  IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ p.primeCompl_le_nonZeroDivisors

/-- The map from `Localization.AtPrime p` to a fraction field `K` of `R` extends `algebraMap R K`.
-/
instance isScalarTower_of_isFractionRing : IsScalarTower R (Localization.AtPrime p) K :=
  IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _
    p.primeCompl_le_nonZeroDivisors

/-- A fraction field of a domain `R` is a fraction field of the localisation of `R` at any prime.
-/
instance isFractionRing : IsFractionRing (Localization.AtPrime p) K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl _ K

end Localization.AtPrime

end
