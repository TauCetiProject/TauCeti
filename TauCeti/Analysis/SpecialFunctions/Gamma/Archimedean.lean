/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Zero values and moduli of the archimedean gamma factors

Mathlib uses total division for the gamma function, so the archimedean factor `Gammaℂ`
has value zero at the nonpositive integers. These are poles of its meromorphic germ.
This characterization complements `Complex.Gammaℝ_eq_zero_iff` for the real factor and
identifies the exceptional values in finite products of shifted gamma factors. Off the real axis
none of `Γ`, `Γ_ℝ` and `Γ_ℂ` vanishes, and a shift `s + μ` stays off the real axis once
`|Im μ| < |Im s|`.

The moduli of the archimedean factors are `‖Γ_ℝ(s)‖ = π^(-Re s / 2) ‖Γ(s / 2)‖` and
`‖Γ_ℂ(s)‖ = 2 (2π)^(-Re s) ‖Γ(s)‖`.
-/

public section

open Real

namespace Complex

/-- The total zero values of the complex archimedean factor occur at the nonpositive integers. -/
theorem Gammaℂ_eq_zero_iff (z : ℂ) : Gammaℂ z = 0 ↔ ∃ n : ℕ, z = -(n : ℂ) := by
  simp [Gammaℂ_def, Real.pi_ne_zero, Gamma_eq_zero_iff]

/-- A shift `s + μ` stays off the real axis when `|Im μ| < |Im s|`. -/
theorem add_im_ne_zero_of_abs_im_lt {s μ : ℂ} (h : |μ.im| < |s.im|) : (s + μ).im ≠ 0 :=
  fun h0 ↦ by
    rw [add_im, ← eq_neg_iff_add_eq_zero] at h0
    rw [h0, abs_neg] at h
    exact h.false

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
