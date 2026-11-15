/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Identities for Deligne's archimedean gamma factors

Mathlib uses total division for the gamma function, so the archimedean factor `Gammaℂ`
has value zero at the nonpositive integers (`Complex.Gammaℂ_eq_zero_iff`), complementing
`Complex.Gammaℝ_eq_zero_iff` for the real factor. This file also records the rescaling identity
`Γ_ℝ(2s) = 2^(s - 1) Γ_ℂ(s)` (`Complex.Gammaℝ_two_mul`), which relates the real gamma factor at
`2s` produced by a two-dimensional Euclidean Gaussian integral at a complex place to Deligne's
complex gamma factor `Γ_ℂ(s) = 2 (2π)^(-s) Γ(s)`.
-/

public section

namespace Complex

/-- The total zero values of the complex archimedean factor occur at the nonpositive integers. -/
theorem Gammaℂ_eq_zero_iff (z : ℂ) : Gammaℂ z = 0 ↔ ∃ n : ℕ, z = -(n : ℂ) := by
  simp [Gammaℂ_def, Real.pi_ne_zero, Gamma_eq_zero_iff]

/-- The real archimedean gamma factor at `2s` is `2 ^ (s - 1)` times the complex archimedean
gamma factor at `s`: `π ^ (-s) Γ(s) = 2 ^ (s - 1) · 2 (2π) ^ (-s) Γ(s)`. -/
theorem Gammaℝ_two_mul (s : ℂ) : Gammaℝ (2 * s) = (2 : ℂ) ^ (s - 1) * Gammaℂ s := by
  have h2pi : ((2 : ℂ) * Real.pi) ^ (-s) = (2 : ℂ) ^ (-s) * (Real.pi : ℂ) ^ (-s) := by
    simpa only [ofReal_ofNat] using mul_cpow_ofReal_nonneg two_pos.le Real.pi_pos.le (-s)
  have h2 : (2 : ℂ) ^ (s - 1) * 2 * (2 : ℂ) ^ (-s) = 1 := by
    have hs : (2 : ℂ) ^ s ≠ 0 := by simp
    rw [sub_eq_add_neg, cpow_add _ _ two_ne_zero, cpow_neg_one, cpow_neg]
    field_simp
  have hexp : -(2 * s) / 2 = -s := by ring
  rw [Gammaℝ_def, Gammaℂ_def, h2pi, hexp, mul_div_cancel_left₀ _ two_ne_zero]
  calc (Real.pi : ℂ) ^ (-s) * Gamma s
      = ((2 : ℂ) ^ (s - 1) * 2 * (2 : ℂ) ^ (-s)) * ((Real.pi : ℂ) ^ (-s) * Gamma s) := by
        rw [h2, one_mul]
    _ = (2 : ℂ) ^ (s - 1) * (2 * ((2 : ℂ) ^ (-s) * (Real.pi : ℂ) ^ (-s)) * Gamma s) := by ring

end Complex
