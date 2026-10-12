/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Basic

/-!
# Fractional ideals of a domain have no zero divisors

Mathlib proves that the submodules of an algebra without zero divisors have no zero divisors and
that the fractional ideals of a Dedekind domain form a cancellative monoid with zero. Between the
two sits the general fact recorded here, pulled back from the submodule instance along the injective
coercion `FractionalIdeal.coeToSubmodule`: the fractional ideals of any commutative ring inside an
algebra without zero divisors have no zero divisors, so a product of nonzero fractional ideals is
nonzero. In particular the nonzero fractional ideals of an order in a number field, which need not
be invertible, form the submonoid `(FractionalIdeal O⁰ K)⁰`.
-/

public section

namespace FractionalIdeal

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P] [Algebra R P]

/-- A product of fractional ideals is zero only if a factor is, when the ambient algebra has no
zero divisors. -/
instance [NoZeroDivisors P] : NoZeroDivisors (FractionalIdeal S P) :=
  coeToSubmodule_injective.noZeroDivisors _ coe_zero coe_mul

end FractionalIdeal
