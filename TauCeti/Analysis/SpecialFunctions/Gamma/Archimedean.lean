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

We also record the elementary identity `2 * (2⁻¹)^s * Gammaℝ (2 * s) = Gammaℂ s` relating the
complex archimedean factor to `Gammaℝ` at `2 * s` (as arises when unfolding Gaussian integrals at
complex places of a number field).
-/

public section

open scoped Real

namespace Complex

/-- The total zero values of the complex archimedean factor occur at the nonpositive integers. -/
theorem Gammaℂ_eq_zero_iff (z : ℂ) : Gammaℂ z = 0 ↔ ∃ n : ℕ, z = -(n : ℂ) := by
  simp [Gammaℂ_def, Real.pi_ne_zero, Gamma_eq_zero_iff]

/-- Expressing `Gammaℂ s` in terms of `Gammaℝ (2 * s)`:
`2 * (2⁻¹)^s * Gammaℝ (2 * s) = Gammaℂ s`. -/
theorem two_mul_inv_two_cpow_mul_Gammaℝ_two_mul (s : ℂ) :
    2 * ((2⁻¹ : ℝ) : ℂ) ^ s * Gammaℝ (2 * s) = Gammaℂ s := by
  have h2 : ((2⁻¹ : ℝ) : ℂ) ^ s = (2 : ℂ) ^ (-s) := by
    rw [ofReal_inv, inv_cpow_ofReal_nonneg zero_le_two, ← cpow_neg, ofReal_ofNat]
  have h2s : -(2 * s) / 2 = -s := by ring
  have h2s' : 2 * s / 2 = s := by ring
  have h2pi : (2 : ℂ) ^ (-s) * (π : ℂ) ^ (-s) = (2 * π) ^ (-s) := by
    simpa using (mul_cpow_ofReal_nonneg zero_le_two Real.pi_pos.le (-s)).symm
  rw [h2, Gammaℝ_def, h2s, h2s', Gammaℂ_def, mul_assoc (2 : ℂ), ← mul_assoc ((2 : ℂ) ^ (-s)),
    h2pi, mul_assoc]

end Complex
