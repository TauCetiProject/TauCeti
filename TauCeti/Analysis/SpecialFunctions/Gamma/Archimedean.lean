/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Relations, zero values and moduli of the archimedean gamma factors

Mathlib defines Deligne's archimedean factors `Gammaℝ s = π ^ (-s / 2) * Gamma (s / 2)` and
`Gammaℂ s = 2 * (2 * π) ^ (-s) * Gamma s` using total division for the gamma function.

* `Complex.Gammaℂ_eq_zero_iff`: the total zero values of `Gammaℂ` occur at the nonpositive
  integers, complementing `Complex.Gammaℝ_eq_zero_iff`. These are poles of its meromorphic germ.
* `Complex.two_mul_Gammaℝ_two_mul`: twice the real factor at `2 * z` is `2 ^ z` times `Gammaℂ z`,
  everywhere on `ℂ` including at the poles where both totalized values vanish.
* Off the real axis none of `Γ`, `Γ_ℝ` and `Γ_ℂ` vanishes.
* The moduli of the archimedean factors are `‖Γ_ℝ(s)‖ = π^(-Re s / 2) ‖Γ(s / 2)‖` and
  `‖Γ_ℂ(s)‖ = 2 (2π)^(-Re s) ‖Γ(s)‖`.
-/

public section

open Real

namespace Complex

/-- The total zero values of the complex archimedean factor occur at the nonpositive integers. -/
theorem Gammaℂ_eq_zero_iff (z : ℂ) : Gammaℂ z = 0 ↔ ∃ n : ℕ, z = -(n : ℂ) := by
  simp [Gammaℂ_def, Real.pi_ne_zero, Gamma_eq_zero_iff]

/-- Twice the real archimedean factor at `2 * z` is `2 ^ z` times the complex archimedean factor
at `z`, including at the nonpositive integers where both sides vanish. -/
theorem two_mul_Gammaℝ_two_mul (z : ℂ) : 2 * Gammaℝ (2 * z) = 2 ^ z * Gammaℂ z := by
  have h2π : ((2 : ℂ) * Real.pi) ^ (-z) = (2 : ℂ) ^ (-z) * (Real.pi : ℂ) ^ (-z) := by
    simpa using ofReal_mul_cpow zero_le_two (Real.pi : ℂ) (-z)
  have h2 : (2 : ℂ) ^ z * (2 : ℂ) ^ (-z) = 1 := by
    rw [← cpow_add _ _ two_ne_zero, add_neg_cancel, cpow_zero]
  rw [Gammaℝ_def, Gammaℂ_def, neg_div, mul_div_cancel_left₀ _ two_ne_zero, h2π]
  linear_combination 2 * (Real.pi : ℂ) ^ (-z) * Gamma z * h2.symm

/-- The gamma function does not vanish off the real axis. -/
theorem Gamma_ne_zero_of_im_ne_zero {s : ℂ} (h : s.im ≠ 0) : Gamma s ≠ 0 :=
  Gamma_ne_zero fun m hm ↦ h (by simp [hm])

/-- The real archimedean factor does not vanish off the real axis. -/
theorem Gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (h : s.im ≠ 0) : Gammaℝ s ≠ 0 := fun h0 ↦ by
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.1 h0
  exact h (by simp [hn])

/-- The complex archimedean factor does not vanish off the real axis. -/
theorem Gammaℂ_ne_zero_of_im_ne_zero {s : ℂ} (h : s.im ≠ 0) : Gammaℂ s ≠ 0 := fun h0 ↦ by
  obtain ⟨n, hn⟩ := (Gammaℂ_eq_zero_iff s).1 h0
  exact h (by simp [hn])

/-- The modulus of the real archimedean gamma factor: `‖Γ_ℝ(s)‖ = π^(-Re s / 2) ‖Γ(s / 2)‖`. -/
theorem norm_Gammaℝ (s : ℂ) : ‖Gammaℝ s‖ = π ^ (-s.re / 2) * ‖Gamma (s / 2)‖ := by
  rw [Gammaℝ_def, norm_mul, norm_cpow_eq_rpow_re_of_pos pi_pos]
  simp [neg_div]

/-- The modulus of the complex archimedean gamma factor: `‖Γ_ℂ(s)‖ = 2 (2π)^(-Re s) ‖Γ(s)‖`. -/
theorem norm_Gammaℂ (s : ℂ) : ‖Gammaℂ s‖ = 2 * (2 * π) ^ (-s.re) * ‖Gamma s‖ := by
  have h2π : (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  rw [Gammaℂ_def, norm_mul, norm_mul, h2π, norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

end Complex
