/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

/-!
# The second-order remainder of the squared positive part

In a linearly ordered commutative ring, the function `x ↦ (max x 0)²` is convex with derivative
`2 max x 0`, and this derivative is `2`-Lipschitz. Its first-order Taylor remainder is therefore
nonnegative and at most quadratic: for all `x` and `y`,

`0 ≤ (max (x + y) 0)² - (max x 0)² - 2 (max x 0) y ≤ y²`

(`TauCeti.max_add_sq_sub_bounds`). On real `L²` this is the pointwise estimate behind the
differentiability of `g ↦ ‖g⁺‖²` (`MeasureTheory.Lp.hasFDerivAt_norm_posPart_sq`).
-/

public section

namespace TauCeti

/-- The remainder `(x + y)⁺² - x⁺² - 2 x⁺ y` of the square of the positive part lies between `0`
and `y²`. -/
theorem max_add_sq_sub_bounds {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (x y : R) :
    0 ≤ max (x + y) 0 ^ 2 - max x 0 ^ 2 - 2 * max x 0 * y ∧
      max (x + y) 0 ^ 2 - max x 0 ^ 2 - 2 * max x 0 * y ≤ y ^ 2 := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 (x + y) with hxy | hxy <;>
    simp only [max_eq_left, max_eq_right, hx, hxy] <;> constructor <;>
    nlinarith [sq_nonneg y, sq_nonneg (x + y), sq_nonneg x]

end TauCeti
