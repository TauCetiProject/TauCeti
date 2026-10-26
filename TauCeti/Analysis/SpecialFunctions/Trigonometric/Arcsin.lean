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

For every real `s`, the double-angle sine `sin (2 * arcsin s)` equals
`2 * s * √(1 - s²)`. Outside `[-1, 1]` both sides vanish. For `-1 ≤ s ≤ 1`,
squaring gives the polynomial `4 * s² * (1 - s²)`.

## Provenance

Adapted from `ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/Gram.lean` in the
[DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization),
released under the Apache 2.0 license.
-/

public section

namespace Real

/-- The double-angle identity `sin (2 * arcsin s) = 2 * s * √(1 - s²)` for all
real `s`. When `|s| ≥ 1`, the square-root factor and both sides are zero. -/
theorem sin_two_mul_arcsin {s : ℝ} :
    sin (2 * arcsin s) = 2 * s * √(1 - s ^ 2) := by
  rw [sin_two_mul, cos_arcsin]
  by_cases h₀ : -1 ≤ s
  · by_cases h₁ : s ≤ 1
    · rw [sin_arcsin h₀ h₁]
    · have hs : 1 < s := lt_of_not_ge h₁
      have hzero : √(1 - s ^ 2) = 0 :=
        sqrt_eq_zero_of_nonpos (by nlinarith [sq_nonneg (s - 1)])
      simp only [hzero, mul_zero]
  · have hs : s < -1 := lt_of_not_ge h₀
    have hzero : √(1 - s ^ 2) = 0 :=
      sqrt_eq_zero_of_nonpos (by nlinarith [sq_nonneg (s + 1)])
    simp only [hzero, mul_zero]

/-- The squared double-angle sine of an angle with sine `s`, as a polynomial:
`sin (2 arcsin s) ^ 2 = 4 s² (1 - s²)`. -/
theorem sin_two_mul_arcsin_sq {s : ℝ} (h₀ : -1 ≤ s) (h₁ : s ≤ 1) :
    sin (2 * arcsin s) ^ 2 = 4 * s ^ 2 * (1 - s ^ 2) := by
  have hnn : (0 : ℝ) ≤ 1 - s ^ 2 := by nlinarith
  rw [sin_two_mul_arcsin, mul_pow, mul_pow, sq_sqrt hnn]
  ring

end Real
