/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Algebra.Field.CrossRatio
import Mathlib.Analysis.Analytic.Constructions
import TauCeti.Analysis.Calculus.Deriv.Mobius

/-!
# Derivatives of the cross-ratio in its first point

The finite cross-ratio `TauCeti.crossRatio w b c d = (w - c) (b - d) / ((w - d) (b - c))`, as a
function of `w`, is the fractional-linear map
`w ↦ ((b - d) w - c (b - d)) / ((b - c) w - d (b - c))`. It has first and second
derivatives `(b - d) (c - d) / ((b - c) (w - d) ^ 2)` and
`-2 (b - d) (c - d) / ((b - c) (w - d) ^ 3)` where `w ≠ d`, and it is analytic
there. For `b = c` the function is constantly `0`, and so are both formulas.

## Main results

* `TauCeti.hasDerivAt_crossRatio_first`, `TauCeti.hasDerivAt_deriv_crossRatio_first`: the first
  and second derivatives of the cross-ratio in its first point.
* `TauCeti.analyticAt_crossRatio_first`: the cross-ratio is analytic in its first point away from
  the fourth.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {b c d z : 𝕜}

/-- The finite cross-ratio as a fractional-linear function of its first point. -/
private theorem crossRatio_first_eq_mul_add_div_mul_add (b c d : 𝕜) :
    (fun w ↦ crossRatio w b c d) =
      fun w ↦ ((b - d) * w + -(c * (b - d))) / ((b - c) * w + -(d * (b - c))) := by
  funext w
  rw [crossRatio_def]
  ring

/-- For `b ≠ c` and `z ≠ d`, the denominator `(b - c) z - d (b - c)` of the fractional-linear
form of the cross-ratio is `(b - c) (z - d)`, a product of two nonzero factors. -/
private theorem crossRatio_first_denom (hbc : b ≠ c) (hz : z ≠ d) :
    b - c ≠ 0 ∧ z - d ≠ 0 ∧ (b - c) * z + -(d * (b - c)) = (b - c) * (z - d) :=
  ⟨sub_ne_zero.mpr hbc, sub_ne_zero.mpr hz, by ring⟩

/-- The finite cross-ratio `crossRatio w b c d = (w - c) (b - d) / ((w - d) (b - c))`, as a
function of its first point, has derivative `(b - d) (c - d) / ((b - c) (z - d) ^ 2)` at `z ≠ d`.
For `b = c` both the function and the derivative are `0`. -/
theorem hasDerivAt_crossRatio_first (hz : z ≠ d) :
    HasDerivAt (fun w ↦ crossRatio w b c d) ((b - d) * (c - d) / ((b - c) * (z - d) ^ 2)) z := by
  rcases eq_or_ne b c with rfl | hbc
  · simpa [crossRatio_self_second_third] using hasDerivAt_const z (0 : 𝕜)
  obtain ⟨hbc', hzd, hden⟩ := crossRatio_first_denom hbc hz
  rw [crossRatio_first_eq_mul_add_div_mul_add]
  refine (hasDerivAt_mul_add_div_mul_add (hden ▸ mul_ne_zero hbc' hzd)).congr_deriv ?_
  rw [hden]
  field_simp [hbc', hzd]
  ring

/-- The derivative of the finite cross-ratio `crossRatio w b c d` in its first point has
derivative `-2 (b - d) (c - d) / ((b - c) (z - d) ^ 3)` at `z ≠ d`. For `b = c` both sides
are `0`. -/
theorem hasDerivAt_deriv_crossRatio_first (hz : z ≠ d) :
    HasDerivAt (deriv fun w ↦ crossRatio w b c d)
      (-2 * (b - d) * (c - d) / ((b - c) * (z - d) ^ 3)) z := by
  rcases eq_or_ne b c with rfl | hbc
  · simpa [crossRatio_self_second_third] using hasDerivAt_const z (0 : 𝕜)
  obtain ⟨hbc', hzd, hden⟩ := crossRatio_first_denom hbc hz
  rw [crossRatio_first_eq_mul_add_div_mul_add]
  refine (hasDerivAt_deriv_mul_add_div_mul_add (hden ▸ mul_ne_zero hbc' hzd)).congr_deriv ?_
  rw [hden]
  field_simp [hbc', hzd]
  ring

/-- The finite cross-ratio `crossRatio w b c d` is analytic in its first point `w` at every
`z ≠ d`. For `b = c` it is constantly `0`. -/
theorem analyticAt_crossRatio_first (hz : z ≠ d) :
    AnalyticAt 𝕜 (fun w ↦ crossRatio w b c d) z := by
  rcases eq_or_ne b c with rfl | hbc
  · simpa [crossRatio_self_second_third] using analyticAt_const (v := (0 : 𝕜))
  obtain ⟨hbc', hzd, hden⟩ := crossRatio_first_denom hbc hz
  rw [crossRatio_first_eq_mul_add_div_mul_add]
  exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
    ((analyticAt_const.mul analyticAt_id).add analyticAt_const) (hden ▸ mul_ne_zero hbc' hzd)

end TauCeti
