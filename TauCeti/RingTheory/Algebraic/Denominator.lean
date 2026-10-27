/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Denominator

/-!
# Denominators of elements integral over `ℤ`

The *denominator* `Algebra.natDenominator x` of an element `x` of a commutative ring is the
absolute value of a generator of the ideal of integers `n` with `n • x` integral over `ℤ`
(`Algebra.natDenominator_dvd_iff`); it is `0` when `x` is transcendental over `ℤ`. An element that
is itself integral over `ℤ` therefore has denominator one
(`Algebra.natDenominator_eq_one_of_isIntegral`): every integer multiple of `x` is then integral
over `ℤ`.

## Main results

* `Algebra.natDenominator_eq_one_of_isIntegral`: an element integral over `ℤ` has denominator `1`.
-/

public section

namespace Algebra

/-- An element integral over `ℤ` has denominator one: every integer multiple of `x` is then
integral over `ℤ`. -/
@[simp]
theorem natDenominator_eq_one_of_isIntegral {S : Type*} [CommRing S] {x : S}
    (hx : IsIntegral ℤ x) : natDenominator x = 1 :=
  Nat.dvd_one.mp (natDenominator_dvd_iff.mpr (by simpa using hx))

end Algebra
