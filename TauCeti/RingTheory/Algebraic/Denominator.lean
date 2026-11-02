/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Algebraic.Denominator
public import Mathlib.RingTheory.Localization.Integral

/-!
# Denominators of integral elements

The *denominator* `Algebra.natDenominator x` of an element `x` of a commutative ring is the
absolute value of a generator of the ideal of integers `n` with `n • x` integral over `ℤ`
(`Algebra.natDenominator_dvd_iff`); it is `0` when `x` is transcendental over `ℤ`. The denominator
of `x` is `1` exactly when `x` is itself integral over `ℤ`
(`Algebra.natDenominator_eq_one_iff`), that is, when every integer multiple of `x` is integral over
`ℤ`. In a `ℚ`-algebra, an element algebraic over `ℚ` is algebraic over `ℤ`, so it has a nonzero
denominator (`Algebra.natDenominator_ne_zero_of_isAlgebraic_rat`).

## Main results

* `Algebra.natDenominator_eq_one_iff`: `natDenominator x = 1` iff `x` is integral over `ℤ`.
* `Algebra.natDenominator_ne_zero_of_isAlgebraic_rat`: the denominator of an element of a
  `ℚ`-algebra that is algebraic over `ℚ` is nonzero.
-/

public section

namespace Algebra

/-- The denominator of `x` is one exactly when `x` is integral over `ℤ`: then every integer
multiple of `x` is integral over `ℤ`. -/
@[simp]
theorem natDenominator_eq_one_iff {S : Type*} [CommRing S] {x : S} :
    natDenominator x = 1 ↔ IsIntegral ℤ x := by
  rw [← Nat.dvd_one, natDenominator_dvd_iff, one_smul]

/-- The denominator of `x` is nonzero when `x` is algebraic over `ℚ`: in a `ℚ`-algebra, being
algebraic over `ℚ` and being algebraic over `ℤ` are equivalent. -/
theorem natDenominator_ne_zero_of_isAlgebraic_rat {S : Type*} [CommRing S] [Algebra ℚ S] {x : S}
    (hx : IsAlgebraic ℚ x) : natDenominator x ≠ 0 :=
  IsAlgebraic.natDenominator_ne_zero ((IsFractionRing.isAlgebraic_iff ℤ ℚ S).2 hx)

end Algebra
