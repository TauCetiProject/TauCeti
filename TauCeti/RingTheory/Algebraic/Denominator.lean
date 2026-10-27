/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Denominator

/-!
# Denominators of integral elements

The *denominator* `Algebra.natDenominator x` of an element `x` of a commutative ring is the
absolute value of a generator of the ideal of integers `n` with `n • x` integral over `ℤ`
(`Algebra.natDenominator_dvd_iff`); it is `0` when `x` is transcendental over `ℤ`. The denominator
of `x` is `1` exactly when `x` is itself integral over `ℤ`
(`Algebra.natDenominator_eq_one_iff`), that is, when every integer multiple of `x` is integral over
`ℤ`.

## Main results

* `Algebra.natDenominator_eq_one_iff`: `natDenominator x = 1` iff `x` is integral over `ℤ`.
-/

public section

namespace Algebra

/-- The denominator of `x` is one exactly when `x` is integral over `ℤ`: then every integer
multiple of `x` is integral over `ℤ`. -/
@[simp]
theorem natDenominator_eq_one_iff {S : Type*} [CommRing S] {x : S} :
    natDenominator x = 1 ↔ IsIntegral ℤ x := by
  rw [← Nat.dvd_one, natDenominator_dvd_iff, one_smul]

end Algebra
