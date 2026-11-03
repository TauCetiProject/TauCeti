/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Arcsine: double-angle identities and a sine substitution

For every real `s`, the double-angle sine `sin (2 * arcsin s)` equals
`2 * s * √(1 - s²)`. Outside `[-1, 1]` both sides vanish. For `-1 ≤ s ≤ 1`,
squaring gives the polynomial `4 * s² * (1 - s²)`.

Inverting the sine also shows that for `0 < φ ≤ π / 2` the map `θ ↦ sin² φ / sin² θ - 1`
sends `(0, φ)` onto `(0, ∞)`; this substitution turns Legendre's elliptic integrals into
Carlson's symmetric integrals.

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

namespace TauCeti

open Real Set

/-- For `0 < φ ≤ π / 2`, the substitution `θ ↦ sin² φ / sin² θ - 1` maps `(0, φ)` onto
`(0, ∞)`. -/
theorem image_sin_sq_div_sin_sq_sub_one_Ioo {φ : ℝ} (hφ0 : 0 < φ) (hφ : φ ≤ π / 2) :
    (fun θ ↦ sin φ ^ 2 / sin θ ^ 2 - 1) '' Ioo 0 φ = Ioi 0 := by
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ0 (by linarith [pi_pos])
  have hs1 : sin φ ≤ 1 := sin_le_one φ
  ext t
  constructor
  · rintro ⟨θ, ⟨hθ0, hθ⟩, rfl⟩
    have hu : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ0 (by linarith [pi_pos])
    have hus : sin θ < sin φ := sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [pi_pos]) hφ hθ
    rw [mem_Ioi, sub_pos, one_lt_div (by positivity)]
    exact pow_lt_pow_left₀ hus hu.le two_ne_zero
  · intro ht
    have ht : (0 : ℝ) < t := ht
    have hr : 1 < √(t + 1) := by
      rw [lt_sqrt zero_le_one]
      linarith
    set x := sin φ / √(t + 1) with hx
    have hx0 : 0 < x := div_pos hs (by linarith)
    have hxs : x < sin φ := div_lt_self hs hr
    refine ⟨arcsin x, ⟨arcsin_pos.mpr hx0, ?_⟩, ?_⟩
    · calc arcsin x < arcsin (sin φ) := arcsin_lt_arcsin (by linarith) hxs (by linarith)
        _ = φ := arcsin_sin (by linarith [pi_pos]) hφ
    · simp only
      rw [sin_arcsin (by linarith) (by linarith), hx, div_pow, sq_sqrt (by linarith)]
      field_simp
      ring

end TauCeti
