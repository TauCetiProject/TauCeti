/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Integral

/-!
# Rings of integers of a valuation are integrally closed in the ambient ring

Let `v` be a valuation on a commutative ring `R` and `O` a ring of integers for `v`
(`Valuation.Integers v O`). Mathlib proves that the integral closure of `O` in `R` is `⊥`
(`Valuation.Integers.integralClosure`); this file records the same content as
`IsIntegrallyClosedIn O R`, the form the integral-closure API consumes, and registers the
instance for the canonical ring of integers `v.integer`.

Mathlib's `Valuation.Integers.isIntegrallyClosed` is a different statement:
`IsIntegrallyClosed O` is a condition on the *fraction field* of `O`, and it is available only
for a valuation of a field. Over a general commutative ring `R` the statement below is the one
that holds.

The instance makes `Subring.integralClosure_le_iff` usable at `v.integer`: a bound `v ≤ 1` on a
subring of `R` becomes a bound on the whole integral closure of that subring in `R`.

## Main results

* `Valuation.Integers.isIntegrallyClosedIn`: a ring of integers `O` of `v` is integrally closed
  in `R`.
* `Valuation.integer.isIntegrallyClosedIn`: the instance for `v.integer`.

-/

public section

namespace Valuation

variable {R : Type*} [CommRing R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **A ring of integers of a valuation is integrally closed in the ambient ring**: if `O` is a
ring of integers for the valuation `v` on `R`, every element of `R` integral over `O` lies in
the image of `O`. -/
theorem Integers.isIntegrallyClosedIn {v : Valuation R Γ₀} {O : Type*} [CommRing O]
    [Algebra O R] (hv : v.Integers O) : IsIntegrallyClosedIn O R :=
  (IsIntegrallyClosedIn.integralClosure_eq_bot_iff R hv.hom_inj).mp hv.integralClosure

/-- **The integers of a valuation are integrally closed in the ambient ring**: an element of `R`
integral over `v.integer` lies in `v.integer`.

This is an instance so that `Subring.integralClosure_le_iff` applies at `v.integer` with no side
goal; that is how a bound on a generating subring is upgraded to a bound on its integral closure
in `R`. -/
instance integer.isIntegrallyClosedIn (v : Valuation R Γ₀) :
    IsIntegrallyClosedIn v.integer R :=
  (integer.integers v).isIntegrallyClosedIn

end Valuation

end
