/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The integral of `|sin|` over a period

The rectified sine `|sin|` is `π`-periodic and equals `sin` on `[0, π]`, so its integral over any
interval of length `π` is `∫_0^π sin = 2`, and over any interval of length `2π` it is `4`.

## Main declarations

* `TauCeti.integral_abs_sin_add_pi`: `∫_a^{a + π} |sin θ| dθ = 2`;
* `TauCeti.integral_abs_sin_add_two_pi`: `∫_a^{a + 2π} |sin θ| dθ = 4`.
-/

public section

open Real Set

namespace TauCeti

/-- **The integral of `|sin|` over a period.** For every real `a`, `∫_a^{a + π} |sin θ| dθ = 2`:
`|sin|` is `π`-periodic, and on `[0, π]` it is `sin`. -/
theorem integral_abs_sin_add_pi (a : ℝ) : ∫ θ in a..a + π, |sin θ| = 2 := by
  have hper : Function.Periodic (fun θ ↦ |sin θ|) π := fun θ ↦ by simp [sin_add_pi]
  rw [hper.intervalIntegral_add_eq a 0, zero_add,
    intervalIntegral.integral_congr fun θ hθ ↦ abs_of_nonneg
      (sin_nonneg_of_nonneg_of_le_pi (uIcc_of_le pi_pos.le ▸ hθ).1 (uIcc_of_le pi_pos.le ▸ hθ).2)]
  simp [integral_sin]
  norm_num

/-- For every real `a`, `∫_a^{a + 2π} |sin θ| dθ = 4`, two periods of `|sin|`. -/
theorem integral_abs_sin_add_two_pi (a : ℝ) : ∫ θ in a..a + 2 * π, |sin θ| = 4 := by
  have hint (b c : ℝ) : IntervalIntegrable (fun θ ↦ |sin θ|) MeasureTheory.volume b c :=
    (continuous_abs.comp continuous_sin).intervalIntegrable b c
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint a (a + π)) (hint _ _),
    integral_abs_sin_add_pi, show a + 2 * π = a + π + π by ring, integral_abs_sin_add_pi]
  norm_num

end TauCeti
