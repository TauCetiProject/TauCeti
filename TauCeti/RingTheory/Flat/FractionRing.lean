/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Fraction fields are flat

A localization of a commutative ring is flat over it (Mathlib's `IsLocalization.flat`). This
cannot be an instance, because the submonoid being inverted is not determined by the two rings.
For a field of fractions it is: `IsFractionRing R K` inverts exactly the nonzerodivisors, so the
flatness of `K` over `R` can be found by instance search. This is how `ℚ_p` is seen to be flat
over `ℤ_p`, which is what makes base change to `ℚ_p` preserve injectivity.

## Main results

* `IsFractionRing.flat`: a field of fractions of `R` is a flat `R`-module.
-/

public section

/-- A field of fractions is flat over its ring: the case of `IsLocalization.flat` in which the
submonoid inverted, the nonzerodivisors, is determined by the rings. -/
instance IsFractionRing.flat (R K : Type*) [CommRing R] [CommRing K] [Algebra R K]
    [IsFractionRing R K] : Module.Flat R K :=
  IsLocalization.flat K (nonZeroDivisors R)
