/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Schur's inequality for ordered triples and weights

For `z ≤ y ≤ x` in a linearly ordered commutative ring and weights `a`, `b`, `c` with `0 ≤ a`,
`0 ≤ c` and `b ≤ a` or `b ≤ c`, the Schur sum

`a (x - y) (x - z) + b (y - z) (y - x) + c (z - x) (z - y)`

is nonnegative. When `b ≤ a` it equals `a (x - y)² + (a - b) (x - y) (y - z) + c (x - z) (y - z)`,
and when `b ≤ c` it equals `c (y - z)² + (c - b) (x - y) (y - z) + a (x - z) (x - y)`; every term
is a product of nonnegative factors. With `0 < a` and `0 < c` the sum vanishes exactly when
`x = z`, that is, when the three points coincide. This is the form of Schur's inequality with
the middle weight dominated by an outer one; Schur's inequality with weights `x ^ t`, `y ^ t`,
`z ^ t` is `TauCeti.schur_inequality`.

## Main results

* `TauCeti.schur_inequality_of_le`: the Schur sum of `z ≤ y ≤ x` is nonnegative.
* `TauCeti.schur_inequality_eq_zero_iff_of_le`: for positive outer weights it vanishes exactly
  when `x = z`.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {a b c x y z : R}

/-- Schur's inequality for ordered points: if `z ≤ y ≤ x`, the outer weights `a`, `c` are
nonnegative and the middle weight satisfies `b ≤ a` or `b ≤ c`, then
`0 ≤ a (x - y) (x - z) + b (y - z) (y - x) + c (z - x) (z - y)`. -/
theorem schur_inequality_of_le (hzy : z ≤ y) (hyx : y ≤ x) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hb : b ≤ a ∨ b ≤ c) :
    0 ≤ a * (x - y) * (x - z) + b * (y - z) * (y - x) + c * (z - x) * (z - y) := by
  have hxy : 0 ≤ x - y := sub_nonneg.2 hyx
  have hyz : 0 ≤ y - z := sub_nonneg.2 hzy
  have hxz : 0 ≤ x - z := add_nonneg hxy hyz |>.trans_eq (sub_add_sub_cancel x y z)
  rcases hb with hb | hb
  · -- The sum is `a (x - y)² + (a - b) (x - y) (y - z) + c (x - z) (y - z)`.
    refine (add_nonneg (add_nonneg (mul_nonneg ha (mul_self_nonneg (x - y)))
      (mul_nonneg (mul_nonneg (sub_nonneg.2 hb) hxy) hyz))
      (mul_nonneg (mul_nonneg hc hxz) hyz)).trans_eq ?_
    ring
  · -- The sum is `c (y - z)² + (c - b) (x - y) (y - z) + a (x - z) (x - y)`.
    refine (add_nonneg (add_nonneg (mul_nonneg hc (mul_self_nonneg (y - z)))
      (mul_nonneg (mul_nonneg (sub_nonneg.2 hb) hxy) hyz))
      (mul_nonneg (mul_nonneg ha hxz) hxy)).trans_eq ?_
    ring

/-- The equality case of Schur's inequality for ordered points: if `z ≤ y ≤ x`, the outer
weights `a`, `c` are positive and `b ≤ a` or `b ≤ c`, then the Schur sum
`a (x - y) (x - z) + b (y - z) (y - x) + c (z - x) (z - y)` vanishes exactly when `x = z`. -/
theorem schur_inequality_eq_zero_iff_of_le (hzy : z ≤ y) (hyx : y ≤ x) (ha : 0 < a)
    (hc : 0 < c) (hb : b ≤ a ∨ b ≤ c) :
    a * (x - y) * (x - z) + b * (y - z) * (y - x) + c * (z - x) * (z - y) = 0 ↔ x = z := by
  refine ⟨fun h ↦ le_antisymm ?_ (hzy.trans hyx), fun h ↦ ?_⟩
  · -- If `z < x`, then `y < x` or `z < y`, and either gap makes the sum positive.
    by_contra! hzx
    have hxy : 0 ≤ x - y := sub_nonneg.2 hyx
    have hyz : 0 ≤ y - z := sub_nonneg.2 hzy
    have hxz : 0 < x - z := sub_pos.2 hzx
    rcases hb with hb | hb
    · have h₁ : 0 ≤ a * (x - y) * (x - y) := mul_nonneg (mul_nonneg ha.le hxy) hxy
      have h₂ : 0 ≤ (a - b) * (x - y) * (y - z) :=
        mul_nonneg (mul_nonneg (sub_nonneg.2 hb) hxy) hyz
      have h₃ : 0 ≤ c * (x - z) * (y - z) := mul_nonneg (mul_nonneg hc.le hxz.le) hyz
      rcases hxy.eq_or_lt with hxy | hxy
      · have : 0 < c * (x - z) * (y - z) := mul_pos (mul_pos hc hxz) (by linarith)
        linarith
      · have : 0 < a * (x - y) * (x - y) := mul_pos (mul_pos ha hxy) hxy
        linarith
    · have h₁ : 0 ≤ c * (y - z) * (y - z) := mul_nonneg (mul_nonneg hc.le hyz) hyz
      have h₂ : 0 ≤ (c - b) * (x - y) * (y - z) :=
        mul_nonneg (mul_nonneg (sub_nonneg.2 hb) hxy) hyz
      have h₃ : 0 ≤ a * (x - z) * (x - y) := mul_nonneg (mul_nonneg ha.le hxz.le) hxy
      rcases hyz.eq_or_lt with hyz | hyz
      · have : 0 < a * (x - z) * (x - y) := mul_pos (mul_pos ha hxz) (by linarith)
        linarith
      · have : 0 < c * (y - z) * (y - z) := mul_pos (mul_pos hc hyz) hyz
        linarith
  · subst h
    obtain rfl : y = x := le_antisymm hyx hzy
    ring

end TauCeti
