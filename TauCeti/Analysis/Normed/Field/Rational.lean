/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Paired rational fractions

The cancellation in `-a² z / (1 - a z)` gives a quadratic norm bound in `a`
when `‖a z‖ ≤ 1/2`. At inverse slopes it equals `1/(z-ρ) + 1/ρ`
away from the two denominators' zeros. These field identities are useful in
logarithmic derivatives of genus-one products.
-/

public section

namespace TauCeti

/-- A quadratic bound for the paired rational term when its denominator stays away from zero. -/
theorem norm_neg_sq_mul_div_one_sub_mul_le {𝕜 : Type*} [NormedField 𝕜]
    {a z : 𝕜} (h : ‖a * z‖ ≤ 1 / 2) :
    ‖-a ^ 2 * z / (1 - a * z)‖ ≤ (2 * ‖z‖) * ‖a‖ ^ 2 := by
  have hden : (1 / 2 : ℝ) ≤ ‖1 - a * z‖ := by
    have ht := norm_sub_norm_le (1 : 𝕜) (a * z)
    rw [norm_one] at ht
    linarith
  calc
    _ = (‖a‖ ^ 2 * ‖z‖) / ‖1 - a * z‖ := by
      rw [norm_div, norm_mul, norm_neg, norm_pow]
    _ ≤ (‖a‖ ^ 2 * ‖z‖) / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ = (2 * ‖z‖) * ‖a‖ ^ 2 := by ring

/-- The inverse-slope paired rational term equals the sum of two reciprocal fractions. -/
theorem neg_inv_sq_mul_div_one_sub_inv_mul {𝕜 : Type*} [Field 𝕜]
    {ρ z : 𝕜} (hρ : ρ ≠ 0) (hz : z ≠ ρ) :
    -(ρ⁻¹) ^ 2 * z / (1 - ρ⁻¹ * z) = 1 / (z - ρ) + 1 / ρ := by
  have hd : 1 - ρ⁻¹ * z ≠ 0 := sub_ne_zero.mpr (by
    intro h
    exact hz ((inv_mul_eq_one₀ hρ).mp h.symm).symm)
  field_simp [hρ, hd, sub_ne_zero.mpr hz]
  ring

end TauCeti
