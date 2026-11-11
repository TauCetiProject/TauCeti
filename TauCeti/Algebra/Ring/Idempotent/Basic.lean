/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination

/-!
# Componentwise arithmetic along an idempotent

An idempotent `e` of a commutative ring `R` splits it as `R ≅ e R × (1 - e) R`. Without reference
to the product decomposition, an element `e x + (1 - e) y` has `e`-component `e x` and
`(1 - e)`-component `(1 - e) y`, and since `e² = e` and `e (1 - e) = 0` such elements multiply
componentwise.

For an idempotent `p` of any ring, `2 p - 1` squares to `1`. For a star projection this is the
self-adjoint unitary `IsStarProjection.two_mul_sub_one_mem_unitary`.

## Main results

* `IsIdempotentElem.mul_add_one_sub_mul`: elements of the form `e x + (1 - e) y` multiply
  componentwise.
* `IsIdempotentElem.two_mul_sub_one_mul_self`: `(2 p - 1) * (2 p - 1) = 1`.
-/

public section

namespace IsIdempotentElem

section CommRing

variable {R : Type*} [CommRing R] {e : R}

/-- **Componentwise multiplication**: for an idempotent `e` of a commutative ring, elements of the
form `e x + (1 - e) y` multiply componentwise, as they would in `e R × (1 - e) R`. -/
theorem mul_add_one_sub_mul (he : IsIdempotentElem e) (x y x' y' : R) :
    (e * x + (1 - e) * y) * (e * x' + (1 - e) * y') = e * (x * x') + (1 - e) * (y * y') := by
  linear_combination (x * x' - x * y' - y * x' + y * y') * he.eq

end CommRing

section Ring

variable {R : Type*} [Ring R] {p : R}

/-- For an idempotent `p`, `2 p - 1` squares to `1`. -/
theorem two_mul_sub_one_mul_self (hp : IsIdempotentElem p) : (2 * p - 1) * (2 * p - 1) = 1 := by
  simp only [two_mul, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one, hp.eq]
  abel

end Ring

end IsIdempotentElem
