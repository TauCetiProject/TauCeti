/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.LinearCombination

/-!
# A square root of `-7` from a seventh root of unity

For a primitive seventh root of unity `ζ` in a domain, the powers `1, ζ, …, ζ ^ 6` sum to zero,
and the Gauss period `ζ + ζ ^ 2 + ζ ^ 4` gives the square root `1 + 2 * (ζ + ζ ^ 2 + ζ ^ 4)`
of `-7`. This is an explicit generator of the quadratic subfield `ℚ(√-7)` of the seventh
cyclotomic field. The identities hold in arbitrary characteristic.

## Main results

* `IsPrimitiveRoot.geom_sum_eq_zero_of_seven`: `1 + ζ + ζ ^ 2 + ⋯ + ζ ^ 6 = 0`.
* `IsPrimitiveRoot.one_add_two_mul_add_sq_add_pow_four_sq_of_seven`:
  `(1 + 2 * (ζ + ζ ^ 2 + ζ ^ 4)) ^ 2 = -7`.

## Reference

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public section

namespace IsPrimitiveRoot

variable {R : Type*} [CommRing R] [IsDomain R] {ζ : R}

/-- The powers `1, ζ, …, ζ ^ 6` of a primitive seventh root of unity `ζ` sum to zero. This is
`IsPrimitiveRoot.geom_sum_eq_zero` with the sum written out. -/
theorem geom_sum_eq_zero_of_seven (hζ : IsPrimitiveRoot ζ 7) :
    1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6 = 0 := by
  simpa [Finset.sum_range_succ] using hζ.geom_sum_eq_zero (by decide)

/-- **A primitive seventh root of unity gives a square root of `-7`**: for the Gauss period
`ζ + ζ ^ 2 + ζ ^ 4`, `(1 + 2 * (ζ + ζ ^ 2 + ζ ^ 4)) ^ 2 = -7`. -/
theorem one_add_two_mul_add_sq_add_pow_four_sq_of_seven (hζ : IsPrimitiveRoot ζ 7) :
    (1 + 2 * (ζ + ζ ^ 2 + ζ ^ 4)) ^ 2 = -7 := by
  linear_combination (4 * ζ ^ 2 - 4 * ζ + 8) * hζ.geom_sum_eq_zero_of_seven

end IsPrimitiveRoot
