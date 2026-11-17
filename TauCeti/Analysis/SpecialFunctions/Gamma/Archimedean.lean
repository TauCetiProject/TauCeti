/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Properties of the complex archimedean gamma factor

Mathlib uses total division for the gamma function, so the archimedean factor `Gammaℂ`
has value zero at the nonpositive integers. These are poles of its meromorphic germ.
This characterization complements `Complex.Gammaℝ_eq_zero_iff` for the real factor and
identifies the exceptional values in finite products of shifted gamma factors.

We also record the elementary identity `Gammaℝ (2 * s) = 2 ^ (s - 1) * Gammaℂ s` relating the
complex archimedean factor to `Gammaℝ` at `2 * s` (as arises when unfolding Gaussian integrals at
complex places of a number field).
-/

public section

open scoped Real

namespace Complex

/-- The total zero values of the complex archimedean factor occur at the nonpositive integers. -/
theorem Gammaℂ_eq_zero_iff (z : ℂ) : Gammaℂ z = 0 ↔ ∃ n : ℕ, z = -(n : ℂ) := by
  simp [Gammaℂ_def, Real.pi_ne_zero, Gamma_eq_zero_iff]

/-- Expressing `Gammaℝ (2 * s)` in terms of `Gammaℂ s`:
`Gammaℝ (2 * s) = 2 ^ (s - 1) * Gammaℂ s`. -/
theorem Gammaℝ_two_mul (s : ℂ) :
    Gammaℝ (2 * s) = (2 : ℂ) ^ (s - 1) * Gammaℂ s := by
  have h2pi : (2 * π : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * (π : ℂ) ^ (-s) := by
    simpa using mul_cpow_ofReal_nonneg zero_le_two Real.pi_pos.le (-s)
  have h2 : (2 : ℂ) ^ (s - 1) * 2 * (2 : ℂ) ^ (-s) = 1 := by
    rw [cpow_sub _ _ two_ne_zero, cpow_one, div_mul_cancel₀ _ two_ne_zero,
      ← cpow_add _ _ two_ne_zero, add_neg_cancel, cpow_zero]
  rw [Gammaℝ_def, Gammaℂ_def, h2pi, neg_div, mul_div_cancel_left₀ _ two_ne_zero]
  calc (π : ℂ) ^ (-s) * Gamma s
      = 1 * ((π : ℂ) ^ (-s) * Gamma s) := (one_mul _).symm
    _ = (2 : ℂ) ^ (s - 1) * 2 * (2 : ℂ) ^ (-s) * ((π : ℂ) ^ (-s) * Gamma s) := by rw [h2]
    _ = _ := by ring

end Complex
