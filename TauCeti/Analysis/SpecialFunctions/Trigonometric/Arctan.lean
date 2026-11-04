/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Basic.Real.Sign

/-!
# Complementary arctangents at the corners of a rectangle

Mathlib's `Real.arctan_inv_of_pos` gives `arctan x⁻¹ = π / 2 - arctan x`; the quotient form
`arctan (u / v) + arctan (v / u) = π / 2` that occurs when the two legs of a right angle are named
separately is not stated there.

## Main results

* `Real.arctan_div_add_arctan_div`: the quotient form of the complementary-angle law.
* `Real.tendsto_arctan_div_nhdsGT_zero`: `arctan (c / η) → (π / 2) * sign c` as `η → 0⁺`.
* `TauCeti.arctan_corner_sum_eq_two_mul_pi_mul_I`: the four corner angles of a rectangle straddling
  the imaginary axis sum to a full turn.
-/

public section

open Complex Filter

open scoped Real Topology

namespace Real

/-- **Complementary angles, in quotient form.**  When `u / v` is positive (for instance when `u`
and `v` are both positive) the angles `arctan (u / v)` and `arctan (v / u)` are complementary. -/
theorem arctan_div_add_arctan_div {u v : ℝ} (h : 0 < u / v) :
    arctan (u / v) + arctan (v / u) = π / 2 := by
  rw [← inv_div u v, arctan_inv_of_pos h]
  ring

/-- As `η → 0⁺`, `arctan (c / η)` tends to `π / 2` times the sign of `c`. -/
theorem tendsto_arctan_div_nhdsGT_zero (c : ℝ) :
    Tendsto (fun η : ℝ => arctan (c / η)) (𝓝[>] 0) (𝓝 (π / 2 * Real.sign c)) := by
  rcases lt_trichotomy c 0 with hc | rfl | hc
  · rw [Real.sign_of_neg hc, mul_neg_one]
    refine (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp ?_
    exact (tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg hc).congr fun η =>
      (div_eq_mul_inv c η).symm
  · simp
  · rw [Real.sign_of_pos hc, mul_one]
    refine (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp ?_
    exact (tendsto_inv_nhdsGT_zero.const_mul_atTop hc).congr fun η => (div_eq_mul_inv c η).symm

end Real

namespace TauCeti

/-- **The corner angles of a rectangle sum to a full turn.**  For a rectangle with vertical sides at
`-B < 0 < c` and horizontal sides at heights `±T`, the four angles subtended at the origin combine
to `2π i`. -/
theorem arctan_corner_sum_eq_two_mul_pi_mul_I {c B T : ℝ} (hc : 0 < c) (hB : 0 < B)
    (hT : 0 < T) :
    2 * I * ((Real.arctan (c / T) : ℂ) - (Real.arctan (-B / T) : ℂ))
      + I * (2 * (Real.arctan (T / c) : ℂ)) - I * (2 * (Real.arctan (T / -B) : ℂ))
      = 2 * π * I := by
  have hc' : (Real.arctan (c / T) : ℂ) + Real.arctan (T / c) = π / 2 :=
    mod_cast Real.arctan_div_add_arctan_div (div_pos hc hT)
  have hB' : (Real.arctan (B / T) : ℂ) + Real.arctan (T / B) = π / 2 :=
    mod_cast Real.arctan_div_add_arctan_div (div_pos hB hT)
  rw [neg_div, Real.arctan_neg, div_neg, Real.arctan_neg]
  push_cast
  linear_combination (2 * I) * hc' + (2 * I) * hB'

end TauCeti
