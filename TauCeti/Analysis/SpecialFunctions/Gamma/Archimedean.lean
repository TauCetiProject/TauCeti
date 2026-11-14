/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Relations and zero values of the archimedean gamma factors

Mathlib defines Deligne's archimedean factors `Gammaℝ s = π ^ (-s / 2) * Gamma (s / 2)` and
`Gammaℂ s = 2 * (2 * π) ^ (-s) * Gamma s` using total division for the gamma function.

* `Complex.Gammaℂ_eq_zero_iff`: the total zero values of `Gammaℂ` occur at the nonpositive
  integers, complementing `Complex.Gammaℝ_eq_zero_iff`.
* `Complex.two_mul_Gammaℝ_two_mul` and `Complex.Gammaℝ_two_mul`: at `2 * z` the real factor
  differs from `Gammaℂ z` by `2 ^ (z - 1)`, everywhere on `ℂ` including at the poles where both
  totalized values vanish.
-/

public section

namespace Complex

/-- The total zero values of the complex archimedean factor occur at the nonpositive integers. -/
theorem Gammaℂ_eq_zero_iff (z : ℂ) : Gammaℂ z = 0 ↔ ∃ n : ℕ, z = -(n : ℂ) := by
  simp [Gammaℂ_def, Real.pi_ne_zero, Gamma_eq_zero_iff]

/-- Twice the real archimedean factor at `2 * z` is `2 ^ z` times the complex archimedean factor
at `z`, including at the nonpositive integers where both sides vanish. -/
theorem two_mul_Gammaℝ_two_mul (z : ℂ) : 2 * Gammaℝ (2 * z) = 2 ^ z * Gammaℂ z := by
  have h2π : ((2 : ℂ) * Real.pi) ^ (-z) = (2 : ℂ) ^ (-z) * (Real.pi : ℂ) ^ (-z) := by
    simpa using mul_cpow_ofReal_nonneg zero_le_two Real.pi_pos.le (-z)
  have h2 : (2 : ℂ) ^ z * (2 : ℂ) ^ (-z) = 1 := by
    rw [← cpow_add _ _ two_ne_zero, add_neg_cancel, cpow_zero]
  rw [Gammaℝ_def, Gammaℂ_def, neg_div, mul_div_cancel_left₀ _ two_ne_zero, h2π]
  linear_combination 2 * (Real.pi : ℂ) ^ (-z) * Gamma z * h2.symm

/-- The real archimedean factor at `2 * z` is `2 ^ (z - 1)` times the complex archimedean factor
at `z`. -/
theorem Gammaℝ_two_mul (z : ℂ) : Gammaℝ (2 * z) = 2 ^ (z - 1) * Gammaℂ z := by
  rw [cpow_sub _ _ two_ne_zero, cpow_one, div_mul_eq_mul_div, eq_div_iff two_ne_zero,
    mul_comm, two_mul_Gammaℝ_two_mul]

end Complex
