/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Integral

/-!
# The integers of a valuation are integrally closed in the ambient ring

For a valuation `v` on a commutative ring `R`, an element of `R` integral over the subring
`v.integer` already lies in `v.integer`. Mathlib proves that content as
`Valuation.Integers.mem_of_integral`; what this file adds is the `IsIntegrallyClosedIn`
instance, which is the form the integral-closure API consumes.

Mathlib's `Valuation.Integers.isIntegrallyClosed_integers` is a different statement:
`IsIntegrallyClosed v.integer` is a condition on the *fraction field* of `v.integer`, and it is
available only for a valuation of a field. Over a general commutative ring `R` the instance
below is the one that holds, and the one a consumer bounding a valuation on an integral closure
inside `R` needs.

Recording it as an instance is what makes `Subring.integralClosure_le_iff` usable at
`v.integer`: a bound `v ≤ 1` on a subring of `R` becomes a bound on the whole integral closure
of that subring in `R` in a single step, with no hand-built `RingHom.codRestrict` into the
valuation ring and no `IsIntegral.map_of_comp_eq` transport.

## Main results

* `Valuation.integer.isIntegrallyClosedIn`: `v.integer` is integrally closed in `R`.

-/

public section

namespace Valuation

variable {R : Type*} [CommRing R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **The integers of a valuation are integrally closed in the ambient ring**: an element of `R`
integral over `v.integer` lies in `v.integer`.

This is an instance rather than a theorem so that `Subring.integralClosure_le_iff` applies at
`v.integer` with no side goal; that is how a bound on a generating subring is upgraded to a
bound on its integral closure in `R`. -/
instance integer.isIntegrallyClosedIn (v : Valuation R Γ₀) :
    IsIntegrallyClosedIn v.integer R :=
  Subring.isIntegrallyClosedIn_iff.mpr fun _ ↦ (integer.integers v).mem_of_integral

end Valuation

end
