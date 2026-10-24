/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Double-angle sine identities for arcsine

For `-1 ≤ s ≤ 1`, the double-angle sine `sin (2 * arcsin s)` is
`2 * s * √(1 - s²)`. Squaring gives the polynomial `4 * s² * (1 - s²)`.
Both formulas hold for either sign of `s`, including the endpoints.

## Provenance

Adapted from `ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/Gram.lean` in the
[DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization),
released under the Apache 2.0 license.
-/

public section

namespace Real

/-- For `-1 ≤ s ≤ 1`, the sine of twice the angle with sine `s` is
`2 * s * √(1 - s²)`. The formula holds for either sign of `s`. -/
theorem sin_two_mul_arcsin {s : ℝ} (h₀ : -1 ≤ s) (h₁ : s ≤ 1) :
    sin (2 * arcsin s) = 2 * s * √(1 - s ^ 2) := by
  rw [sin_two_mul, sin_arcsin h₀ h₁, cos_arcsin]

/-- The squared double-angle sine of an angle with sine `s`, as a polynomial:
`sin (2 arcsin s) ^ 2 = 4 s² (1 - s²)`. -/
theorem sin_two_mul_arcsin_sq {s : ℝ} (h₀ : -1 ≤ s) (h₁ : s ≤ 1) :
    sin (2 * arcsin s) ^ 2 = 4 * s ^ 2 * (1 - s ^ 2) := by
  have hnn : (0 : ℝ) ≤ 1 - s ^ 2 := by nlinarith
  rw [sin_two_mul_arcsin h₀ h₁, mul_pow, mul_pow, sq_sqrt hnn]
  ring

end Real
