/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Zero values and duplication of the archimedean gamma factors

Mathlib uses total division for the gamma function, so the archimedean factor `Gammaℂ`
has value zero at the nonpositive integers. These are poles of its meromorphic germ.
This characterization complements `Complex.Gammaℝ_eq_zero_iff` for the real factor and
identifies the exceptional values in finite products of shifted gamma factors.

At twice an argument, the real factor `Gammaℝ (2 * z) = π ^ (-z) * Gamma z` differs from
Deligne's complex factor `Gammaℂ z = 2 * (2 * π) ^ (-z) * Gamma z` by the power `2 ^ (z - 1)`
(`Complex.Gammaℝ_two_mul`). This is the factor relating the Euclidean complex-place Mellin
integral of `exp (-π t |w|²)` to `Gammaℂ`.
-/

public section

namespace Complex

/-- The total zero values of the complex archimedean factor occur at the nonpositive integers. -/
theorem Gammaℂ_eq_zero_iff (z : ℂ) : Gammaℂ z = 0 ↔ ∃ n : ℕ, z = -(n : ℂ) := by
  simp [Gammaℂ_def, Real.pi_ne_zero, Gamma_eq_zero_iff]

/-- The real archimedean gamma factor at `2 * z` is `2 ^ (z - 1)` times Deligne's complex
archimedean gamma factor at `z`, including at the nonpositive integers where both sides vanish. -/
theorem Gammaℝ_two_mul (z : ℂ) : Gammaℝ (2 * z) = (2 : ℂ) ^ (z - 1) * Gammaℂ z := by
  have h2 : (2 : ℂ) ^ (z - 1) * 2 * (2 : ℂ) ^ (-z) = 1 := by
    calc (2 : ℂ) ^ (z - 1) * 2 * (2 : ℂ) ^ (-z)
        = (2 : ℂ) ^ (z - 1) * (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (-z) := by simp
      _ = (2 : ℂ) ^ (z - 1 + 1 + -z) := by
          rw [← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero]
      _ = 1 := by
          have hexp : z - 1 + 1 + -z = 0 := by ring
          rw [hexp, cpow_zero]
  have h2π : (2 * Real.pi : ℂ) ^ (-z) = (2 : ℂ) ^ (-z) * (Real.pi : ℂ) ^ (-z) := by
    simpa only [ofReal_ofNat] using TauCeti.ofReal_mul_cpow zero_le_two (Real.pi : ℂ) (-z)
  have hdiv : -(2 * z) / 2 = -z := by ring
  rw [Gammaℝ_def, Gammaℂ_def, hdiv, mul_div_cancel_left₀ z two_ne_zero, h2π]
  symm
  calc (2 : ℂ) ^ (z - 1) * (2 * ((2 : ℂ) ^ (-z) * (Real.pi : ℂ) ^ (-z)) * Gamma z)
      = ((2 : ℂ) ^ (z - 1) * 2 * (2 : ℂ) ^ (-z)) * ((Real.pi : ℂ) ^ (-z) * Gamma z) := by ring
    _ = 1 * ((Real.pi : ℂ) ^ (-z) * Gamma z) := by rw [h2]
    _ = (Real.pi : ℂ) ^ (-z) * Gamma z := one_mul _

/-- Deligne's complex archimedean gamma factor expressed in terms of `Gammaℝ (2 * z)`. -/
theorem Gammaℂ_eq_two_cpow_mul_Gammaℝ (z : ℂ) :
    Gammaℂ z = (2 : ℂ) ^ (1 - z) * Gammaℝ (2 * z) := by
  rw [Gammaℝ_two_mul, ← mul_assoc, ← cpow_add _ _ two_ne_zero]
  have hexp : 1 - z + (z - 1) = 0 := by ring
  rw [hexp, cpow_zero, one_mul]

end Complex
