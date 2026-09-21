/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Linear fractional transformations over a field

A linear fractional transformation `t ↦ (a * t + b) / (c * t + d)` over a field `𝕜` is
determined by its coefficient matrix `!![a, b; c, d]`, and the determinant `a * d - b * c`
controls how it separates points. This file records the algebraic identity behind that: if the
transformation fixes `w`, then it scales the displacement `t - w` by
`(a * d - b * c) / ((c * t + d) * (c * w + d))`.

This is the computation that linearizes a linear fractional transformation at a fixed point.
Over `ℂ` it is what turns a Möbius transformation of the upper half-plane fixing a point into a
rotation of the disc coordinate centred there, in
`TauCeti/Analysis/Complex/UpperHalfPlane/DiscCoordinate.lean`.

## Main results

* `TauCeti.moebius_sub_of_fixed`: the difference formula for a linear fractional
  transformation at a fixed point.
-/

public section

namespace TauCeti

/-- The Möbius difference formula at a fixed point: if `(a * w + b) / (c * w + d) = w`, then
`(a * t + b) / (c * t + d) - w = (a * d - b * c) * (t - w) / ((c * t + d) * (c * w + d))`. -/
theorem moebius_sub_of_fixed {𝕜 : Type*} [Field 𝕜] {a b c d w t : 𝕜}
    (hw : a * w + b = w * (c * w + d)) (hj : c * w + d ≠ 0) (hjt : c * t + d ≠ 0) :
    (a * t + b) / (c * t + d) - w =
      (a * d - b * c) * (t - w) / ((c * t + d) * (c * w + d)) := by
  rw [div_sub' hjt, div_eq_div_iff hjt (mul_ne_zero hjt hj)]
  linear_combination (c * t + d) ^ 2 * hw

end TauCeti
