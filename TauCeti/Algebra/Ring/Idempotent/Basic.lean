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
self-adjoint unitary `IsStarProjection.two_mul_sub_one_mem_unitary`. Conversely, for any element
`u` with `u * u = 1`, `1 + u` squares to `(1 + u) + (1 + u)`, and when `v` anticommutes with `u`
(`u * v + v * u = 0`), the sandwich `(1 + u) * (1 + v) * (1 + u)` also reduces to
`(1 + u) + (1 + u)`.

## Main results

* `IsIdempotentElem.mul_add_one_sub_mul`: elements of the form `e x + (1 - e) y` multiply
  componentwise.
* `IsIdempotentElem.two_mul_sub_one_mul_self`: `(2 p - 1) * (2 p - 1) = 1`.
* `TauCeti.one_add_mul_self_of_mul_self_eq_one`: if `u * u = 1`, then
  `(1 + u) * (1 + u) = (1 + u) + (1 + u)`.
* `TauCeti.one_add_mul_one_add_mul_one_add_of_mul_self_eq_one`: if `u * u = 1` and
  `u * v + v * u = 0`, then `(1 + u) * (1 + v) * (1 + u) = (1 + u) + (1 + u)`.
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

namespace TauCeti

/-- If `u * u = 1`, then `1 + u` squares to `(1 + u) + (1 + u)` (so after dividing by `2`,
`2⁻¹ • (1 + u)` is idempotent). -/
theorem one_add_mul_self_of_mul_self_eq_one {R : Type*} [NonAssocSemiring R] {u : R}
    (hu : u * u = 1) :
    (1 + u) * (1 + u) = (1 + u) + (1 + u) := by
  rw [add_mul, one_mul, mul_add, mul_one, hu, add_comm u 1]

/-- If `u * u = 1` and `u * v + v * u = 0`, then `(1 + u) * (1 + v) * (1 + u)` reduces to
`(1 + u) + (1 + u)`. -/
theorem one_add_mul_one_add_mul_one_add_of_mul_self_eq_one {R : Type*} [Semiring R] {u v : R}
    (hu : u * u = 1) (huv : u * v + v * u = 0) :
    (1 + u) * (1 + v) * (1 + u) = (1 + u) + (1 + u) := by
  have hv : v + u * v * u = 0 :=
    calc
      v + u * v * u = 1 * v + u * (v * u) := by rw [one_mul, mul_assoc]
      _ = u * u * v + u * (v * u) := by rw [hu]
      _ = u * (u * v + v * u) := by rw [mul_assoc, mul_add]
      _ = 0 := by rw [huv, mul_zero]
  calc
    (1 + u) * (1 + v) * (1 + u)
        = ((1 + u) + (u + u * u)) + (u * v + v * u) + (v + u * v * u) := by
          simp only [add_mul, mul_add, one_mul, mul_one]
          ac_rfl
    _ = (1 + u) + (1 + u) := by
          rw [hu, huv, hv, add_zero, add_zero, add_comm u 1]

end TauCeti
