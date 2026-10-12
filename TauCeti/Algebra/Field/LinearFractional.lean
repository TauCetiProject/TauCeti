/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

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
* `TauCeti.crossRatio_comp_eq_of_sub_eq_div`: maps with factorized differences preserve
  cross-ratios.
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

/-- **Maps with factorized difference quotients preserve cross-ratios.** If
`φ s - φ t = κ * (s - t) / (d s * d t)` for all `s` and `t` in `S`, with `κ` and the values of `d`
on `S` nonzero, then `φ` preserves the cross-ratio `(p - r) * (q - s) / ((p - s) * (q - r))` of any
four points of `S`. Möbius transformations have difference quotients of this form. -/
theorem crossRatio_comp_eq_of_sub_eq_div {𝕜 : Type*} [Field 𝕜] {φ d : 𝕜 → 𝕜} {κ : 𝕜}
    {S : Set 𝕜} (hκ : κ ≠ 0) (hd : ∀ t ∈ S, d t ≠ 0)
    (hφ : ∀ s ∈ S, ∀ t ∈ S, φ s - φ t = κ * (s - t) / (d s * d t))
    {p q r s : 𝕜} (hp : p ∈ S) (hq : q ∈ S) (hr : r ∈ S) (hs : s ∈ S) :
    (φ p - φ r) * (φ q - φ s) / ((φ p - φ s) * (φ q - φ r)) =
      (p - r) * (q - s) / ((p - s) * (q - r)) := by
  have hL : κ ^ 2 / (d p * d q * d r * d s) ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 hκ)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (hd p hp) (hd q hq)) (hd r hr)) (hd s hs))
  have hnum : κ * (p - r) / (d p * d r) * (κ * (q - s) / (d q * d s)) =
      (p - r) * (q - s) * (κ ^ 2 / (d p * d q * d r * d s)) := by ring
  have hden : κ * (p - s) / (d p * d s) * (κ * (q - r) / (d q * d r)) =
      (p - s) * (q - r) * (κ ^ 2 / (d p * d q * d r * d s)) := by ring
  rw [hφ p hp r hr, hφ q hq s hs, hφ p hp s hs, hφ q hq r hr,
    hnum, hden, mul_div_mul_right _ _ hL]

end TauCeti
