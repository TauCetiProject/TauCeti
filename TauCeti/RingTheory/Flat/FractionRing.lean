/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Flatness of localizations at nonzerodivisors

An `IsFractionRing R K` algebra is a localization of the commutative semiring `R` at its
nonzerodivisors. Mathlib's `IsLocalization.flat` proves that every localization is flat over
its base, but its submonoid parameter prevents using it as a general instance. For
`IsFractionRing R K`, the inverted submonoid is determined by `R`, so this specialization
makes the flatness of `K` over `R` available to instance search.

This applies to `ℚ≥0` over `ℕ`, fraction fields, and total quotient rings of rings with zero
divisors. In particular, `ℚ_p` is flat over `ℤ_p`, which makes base change to `ℚ_p` preserve
injectivity. Through `ℚ`, every `ℚ`-algebra is flat over `ℤ` (`algebraRat.flat_int`).

## Main results

* `IsFractionRing.flat`: a localization of `R` at its nonzerodivisors is a flat `R`-module.
* `algebraRat.flat_int`: a `ℚ`-algebra is a flat `ℤ`-module.
-/

public section

/-- A localization at the nonzerodivisors of a commutative semiring is flat over that semiring. -/
instance IsFractionRing.flat (R K : Type*) [CommSemiring R] [CommSemiring K] [Algebra R K]
    [IsFractionRing R K] : Module.Flat R K :=
  IsLocalization.flat K (nonZeroDivisors R)

/-- A `ℚ`-algebra is flat over `ℤ`: it is flat over the localization `ℚ` of `ℤ`. -/
theorem algebraRat.flat_int (R : Type*) [Ring R] [Algebra ℚ R] : Module.Flat ℤ R :=
  (Module.flat_iff_of_isLocalization ℚ (nonZeroDivisors ℤ) R).1 inferInstance
