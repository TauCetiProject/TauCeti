/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith

/-!
# Bounding a sum through a two-step linear estimate

If `U ≤ p Z + q Y` and `Y ≤ r (a Z + b W)` with nonnegative coefficients, then `U + Y` is bounded by
a multiple of `Z + W`: substitute the second estimate into the first.

## Main results

* `TauCeti.add_le_mul_add_of_le_of_le`: `U + Y ≤ (p + (q + 1) r (a + b)) (Z + W)` from
  `U ≤ p Z + q Y` and `Y ≤ r (a Z + b W)`.
-/

public section

namespace TauCeti

/-- If `U ≤ p Z + q Y` and `Y ≤ r (a Z + b W)`, where `p, q, r, a, b, Z, W` are nonnegative, then
`U + Y ≤ (p + (q + 1) r (a + b)) (Z + W)`. -/
theorem add_le_mul_add_of_le_of_le {α : Type*} [CommRing α] [LinearOrder α]
    [IsStrictOrderedRing α] {U Y Z W p q r a b : α} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hZ : 0 ≤ Z) (hW : 0 ≤ W)
    (hX : U ≤ p * Z + q * Y) (hY : Y ≤ r * (a * Z + b * W)) :
    U + Y ≤ (p + (q + 1) * r * (a + b)) * (Z + W) := by
  have hk : 0 ≤ (q + 1) * r := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hY (by positivity : (0 : α) ≤ q + 1),
    mul_nonneg (mul_nonneg hk hb) hZ, mul_nonneg (mul_nonneg hk ha) hW,
    mul_nonneg hp hW]

end TauCeti
