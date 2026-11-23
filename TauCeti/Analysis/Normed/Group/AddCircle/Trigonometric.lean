/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Trigonometric bounds on `UnitAddCircle`

This file records Jordan's sine lower bounds relating the circle norm on `UnitAddCircle = ℝ / ℤ`
to `|sin (π * t)|`:

* `Real.two_mul_norm_unitAddCircle_le_abs_sin`: `2 * ‖(t : UnitAddCircle)‖ ≤ |sin (π * t)|`.
* `Real.four_mul_norm_unitAddCircle_sq_le_sin_sq`:
  `4 * ‖(t : UnitAddCircle)‖ ^ 2 ≤ sin (π * t) ^ 2`.
-/

public section

namespace Real

/-- Jordan's sine lower bound on `UnitAddCircle = ℝ / ℤ`:
`2 * ‖(t : UnitAddCircle)‖ ≤ |sin (π * t)|`. -/
theorem two_mul_norm_unitAddCircle_le_abs_sin (t : ℝ) :
    2 * ‖(t : UnitAddCircle)‖ ≤ |Real.sin (Real.pi * t)| := by
  set u : ℝ := t - round t
  have hu : ‖(t : UnitAddCircle)‖ = |u| := UnitAddCircle.norm_eq
  have hle : |u| ≤ 1 / 2 := abs_sub_round t
  have hsin_le : 2 * |u| ≤ Real.sin (Real.pi / 2 * (2 * |u|)) :=
    Real.le_sin_mul (by positivity) (by linarith)
  have harg : Real.pi / 2 * (2 * |u|) = Real.pi * |u| := by ring
  have habs_u : |Real.sin (Real.pi * |u|)| = |Real.sin (Real.pi * u)| := by
    rcases abs_cases u with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, mul_neg, Real.sin_neg, abs_neg]
  have habs_t : |Real.sin (Real.pi * u)| = |Real.sin (Real.pi * t)| := by
    have hsub : Real.pi * u = Real.pi * t - (round t : ℤ) * Real.pi := by
      simp only [u]; ring
    rw [hsub]
    simp [Real.sin_sub_int_mul_pi, abs_mul]
  calc
    2 * ‖(t : UnitAddCircle)‖ = 2 * |u| := by rw [hu]
    _ ≤ Real.sin (Real.pi * |u|) := harg ▸ hsin_le
    _ ≤ |Real.sin (Real.pi * |u|)| := le_abs_self _
    _ = |Real.sin (Real.pi * t)| := habs_u.trans habs_t

/-- Squared form of Jordan's sine lower bound on `UnitAddCircle`:
`4 * ‖(t : UnitAddCircle)‖ ^ 2 ≤ sin (π * t) ^ 2`. -/
theorem four_mul_norm_unitAddCircle_sq_le_sin_sq (t : ℝ) :
    4 * ‖(t : UnitAddCircle)‖ ^ 2 ≤ Real.sin (Real.pi * t) ^ 2 := by
  nlinarith [t.two_mul_norm_unitAddCircle_le_abs_sin, sq_abs (Real.sin (Real.pi * t)),
    norm_nonneg (t : UnitAddCircle)]

end Real
