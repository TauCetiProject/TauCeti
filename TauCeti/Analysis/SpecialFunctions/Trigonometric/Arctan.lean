/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Complementary arctangents and arctangents of quotients

Mathlib's `Real.arctan_inv_of_pos` gives `arctan x⁻¹ = π / 2 - arctan x`; the quotient form
`arctan (u / v) + arctan (v / u) = π / 2` that occurs when the two legs of a right angle are named
separately is not stated there.

As `η` decreases to `0`, the angle `arctan (c / η)` tends to `π / 2` or `-(π / 2)` according to
the sign of `c`. These limits describe the vanishing-width limit of the Cauchy (Poisson) kernel
`η / (η² + x²)`, whose integrals are differences of such arctangents.

## Main results

* `Real.arctan_div_add_arctan_div`: the quotient form of the complementary-angle law.
* `Real.tendsto_arctan_div_nhdsGT_zero_of_pos`, `Real.tendsto_arctan_div_nhdsGT_zero_of_neg`:
  the limits of `arctan (c / η)` as `η` decreases to `0`.
* `Real.tendsto_inv_pi_mul_arctan_sub_arctan`: the normalized angle subtended by `[a, b]` at
  `x + iη` tends to the indicator of `[a, b]` with half weights at the endpoints.
* `TauCeti.arctan_corner_sum_eq_two_mul_pi_mul_I`: the four corner angles of a rectangle straddling
  the imaginary axis sum to a full turn.
-/

public section

open Complex Filter

open scoped Real Topology

namespace Real

/-- **Complementary angles, in quotient form.**  For positive `u` and `v` the angles
`arctan (u / v)` and `arctan (v / u)` are complementary. -/
theorem arctan_div_add_arctan_div {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    arctan (u / v) + arctan (v / u) = π / 2 := by
  rw [← inv_div u v, Real.arctan_inv_of_pos (by positivity)]
  ring

/-- For positive `c`, `arctan (c / η)` tends to `π / 2` as `η` decreases to `0`. -/
theorem tendsto_arctan_div_nhdsGT_zero_of_pos {c : ℝ} (hc : 0 < c) :
    Tendsto (fun η : ℝ => arctan (c / η)) (𝓝[>] 0) (𝓝 (π / 2)) := by
  have h : Tendsto (fun η : ℝ => c / η) (𝓝[>] 0) atTop := by
    simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop hc
  exact (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h

/-- For negative `c`, `arctan (c / η)` tends to `-(π / 2)` as `η` decreases to `0`. -/
theorem tendsto_arctan_div_nhdsGT_zero_of_neg {c : ℝ} (hc : c < 0) :
    Tendsto (fun η : ℝ => arctan (c / η)) (𝓝[>] 0) (𝓝 (-(π / 2))) := by
  have h : Tendsto (fun η : ℝ => c / η) (𝓝[>] 0) atBot := by
    simpa only [div_eq_mul_inv] using tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg hc
  exact (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp h

/-- The normalized angle subtended by `[a, b]` at `x + iη` tends, as `η ↓ 0`, to `1` on `(a, b)`,
to `1 / 2` at the endpoints and to `0` outside `[a, b]`. -/
theorem tendsto_inv_pi_mul_arctan_sub_arctan {a b : ℝ} (hab : a < b) (x : ℝ) :
    Tendsto (fun η : ℝ => π⁻¹ * (arctan ((b - x) / η) - arctan ((a - x) / η))) (𝓝[>] 0)
      (𝓝 ((Set.Ioo a b).indicator 1 x +
        (({a} : Set ℝ).indicator 1 x + ({b} : Set ℝ).indicator 1 x) / 2)) := by
  have key {L₁ L₂ : ℝ} (h₁ : Tendsto (fun η : ℝ => arctan ((b - x) / η)) (𝓝[>] 0) (𝓝 L₁))
      (h₂ : Tendsto (fun η : ℝ => arctan ((a - x) / η)) (𝓝[>] 0) (𝓝 L₂))
      (hL : π⁻¹ * (L₁ - L₂) = (Set.Ioo a b).indicator 1 x +
        (({a} : Set ℝ).indicator 1 x + ({b} : Set ℝ).indicator 1 x) / 2) :
      Tendsto (fun η : ℝ => π⁻¹ * (arctan ((b - x) / η) - arctan ((a - x) / η))) (𝓝[>] 0)
        (𝓝 ((Set.Ioo a b).indicator 1 x +
          (({a} : Set ℝ).indicator 1 x + ({b} : Set ℝ).indicator 1 x) / 2)) :=
    hL ▸ (h₁.sub h₂).const_mul π⁻¹
  rcases lt_trichotomy x a with hxa | rfl | hax
  · refine key (tendsto_arctan_div_nhdsGT_zero_of_pos (by linarith))
      (tendsto_arctan_div_nhdsGT_zero_of_pos (by linarith)) ?_
    simp [hxa.ne, (hxa.trans hab).ne, not_lt.2 hxa.le]
  · refine key (L₂ := 0) (tendsto_arctan_div_nhdsGT_zero_of_pos (by linarith)) (by simp) ?_
    simp only [sub_zero, Set.mem_Ioo, lt_self_iff_false, false_and, not_false_eq_true,
      Set.indicator_of_notMem, Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply, hab.ne,
      add_zero, one_div, zero_add]
    field_simp
  · rcases lt_trichotomy x b with hxb | rfl | hbx
    · refine key (tendsto_arctan_div_nhdsGT_zero_of_pos (by linarith))
        (tendsto_arctan_div_nhdsGT_zero_of_neg (by linarith)) ?_
      simp [hax, hxb, hax.ne', hxb.ne]
    · refine key (L₁ := 0) (by simp) (tendsto_arctan_div_nhdsGT_zero_of_neg (by linarith)) ?_
      simp only [sub_neg_eq_add, zero_add, Set.mem_Ioo, lt_self_iff_false, and_false,
        not_false_eq_true, Set.indicator_of_notMem, Set.mem_singleton_iff, hab.ne',
        Set.indicator_of_mem, Pi.one_apply, one_div]
      field_simp
    · refine key (tendsto_arctan_div_nhdsGT_zero_of_neg (by linarith))
        (tendsto_arctan_div_nhdsGT_zero_of_neg (by linarith)) ?_
      simp [hbx.ne', (hab.trans hbx).ne', not_lt.2 hbx.le]

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
  have hA : ((Real.arctan (c / T) : ℝ) : ℂ) + ((Real.arctan (T / c) : ℝ) : ℂ) = (π : ℂ) / 2 := by
    rw [← Complex.ofReal_add, Real.arctan_div_add_arctan_div hc hT]
    push_cast
    ring
  have hB' : ((Real.arctan (B / T) : ℝ) : ℂ) + ((Real.arctan (T / B) : ℝ) : ℂ) = (π : ℂ) / 2 := by
    rw [← Complex.ofReal_add, Real.arctan_div_add_arctan_div hB hT]
    push_cast
    ring
  rw [neg_div, Real.arctan_neg, div_neg, Real.arctan_neg]
  push_cast
  linear_combination (2 * I) * hA + (2 * I) * hB'

end TauCeti
