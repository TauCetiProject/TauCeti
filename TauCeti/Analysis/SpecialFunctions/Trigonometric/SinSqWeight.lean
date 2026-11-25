/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The sine-squared interpolation weight

The weight `TauCeti.sinSqWeight t = sin (π t / 2) ^ 2` rises from `0` at `t = 0` to `1` at
`t = 1` and takes its values in `[0, 1]`. It is analytic, unlike `Real.smoothTransition`, which is
only `C^∞`. So it reparametrizes the time of interpolations `x + w t • (f x - x)` of every
regularity `C^k`, `k : ℕ∞ω`, including `C^ω`.

## Main results

* `TauCeti.sinSqWeight_zero`, `TauCeti.sinSqWeight_one`: the end values.
* `TauCeti.sinSqWeight_mem`, `TauCeti.norm_sinSqWeight_le_one`: the values lie in `[0, 1]`.
* `TauCeti.contDiff_sinSqWeight`: the weight is `C^k` for every `k : ℕ∞ω`.
-/

public section

noncomputable section

open Set
open scoped ContDiff

namespace TauCeti

/-- The weight `sin (π t / 2) ^ 2`, rising analytically from `0` at `t = 0` to `1` at `t = 1`. -/
def sinSqWeight (t : ℝ) : ℝ := Real.sin (Real.pi * t / 2) ^ 2

/-- The defining formula of `TauCeti.sinSqWeight`. -/
theorem sinSqWeight_def (t : ℝ) : sinSqWeight t = Real.sin (Real.pi * t / 2) ^ 2 :=
  (rfl)

/-- The weight vanishes at `0`. -/
@[simp]
theorem sinSqWeight_zero : sinSqWeight 0 = 0 := by simp [sinSqWeight_def]

/-- The weight is `1` at `1`. -/
@[simp]
theorem sinSqWeight_one : sinSqWeight 1 = 1 := by simp [sinSqWeight_def]

/-- The weight takes its values in `[0, 1]`. -/
theorem sinSqWeight_mem (t : ℝ) : sinSqWeight t ∈ Icc 0 1 :=
  ⟨sq_nonneg _, Real.sin_sq_le_one _⟩

/-- The weight has norm at most one. -/
theorem norm_sinSqWeight_le_one (t : ℝ) : ‖sinSqWeight t‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (sinSqWeight_mem t).1]
  exact (sinSqWeight_mem t).2

/-- The weight is analytic, so `C^k` for every `k : ℕ∞ω`. -/
theorem contDiff_sinSqWeight {k : ℕ∞ω} : ContDiff ℝ k sinSqWeight :=
  (Real.contDiff_sin.comp ((contDiff_const.mul contDiff_id).div_const 2)).pow 2

end TauCeti
