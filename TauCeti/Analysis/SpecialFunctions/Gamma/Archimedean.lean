/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Zero locus, regularity, and norms of the archimedean gamma factors

Deligne's archimedean factors are
$$\Gamma_{\mathbb{R}}(s) = \pi^{-s/2} \Gamma(s/2), \qquad
  \Gamma_{\mathbb{C}}(s) = 2 (2\pi)^{-s} \Gamma(s).$$
Mathlib uses total division for the gamma function, so `Gammaℝ` and `Gammaℂ` take the junk value
`0` at their poles `-2n` and `-n` (`n : ℕ`) and are nonzero everywhere else; in particular neither
vanishes off the real axis. Because their reciprocals are entire (`differentiable_Gammaℝ_inv` and
`differentiable_Gammaℂ_inv`), both factors are complex-differentiable wherever they are nonzero.

Since the bases `π` and `2π` are positive reals, their complex powers have norms `π ^ (-s.re / 2)`
and `(2π) ^ (-s.re)`. Taking norms and real logarithms separates those exponential prefactors from
`‖Γ(s / 2)‖` and `‖Γ(s)‖`, preparing the vertical-strip Stirling asymptotics of `Gammaℝ`,
`Gammaℂ`, and finite products of shifted factors.

## Main declarations

* `Complex.Gammaℂ_eq_zero_iff`: total zeros of `Gammaℂ` occur at `-(n : ℂ)` (`n : ℕ`).
* `Complex.Gamma_ne_zero_of_im_ne_zero`, `Complex.Gammaℝ_ne_zero_of_im_ne_zero`,
  `Complex.Gammaℂ_ne_zero_of_im_ne_zero`: nonvanishing off the real axis.
* `Complex.differentiableAt_Gammaℝ`, `Complex.differentiableAt_Gammaℂ`,
  `Complex.continuousAt_Gammaℝ`, `Complex.continuousAt_Gammaℂ`: regularity away from the poles.
* `Complex.norm_Gammaℝ`, `Complex.norm_Gammaℂ`, `Complex.log_norm_Gammaℝ`,
  `Complex.log_norm_Gammaℂ`: norm and log-norm identities.

## References

* P. Deligne, *Valeurs de fonctions L et périodes d'intégrales*, Proc. Symp. Pure Math. 33 (1979),
  Part 2, §5.3.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1.
-/

public section

namespace Complex

/-- The total zero values of the complex archimedean factor occur at the nonpositive integers. -/
theorem Gammaℂ_eq_zero_iff (z : ℂ) : Gammaℂ z = 0 ↔ ∃ n : ℕ, z = -(n : ℂ) := by
  simp [Gammaℂ_def, Real.pi_ne_zero, Gamma_eq_zero_iff]

/-- `Complex.Gamma` does not vanish off the real axis. -/
theorem Gamma_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Gamma z ≠ 0 :=
  Gamma_ne_zero fun n hn ↦ hz (by simp [hn])

/-- Deligne's real archimedean factor `Gammaℝ` does not vanish off the real axis. -/
theorem Gammaℝ_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Gammaℝ z ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff]
  rintro ⟨n, hn⟩
  exact hz (by simp [hn])

/-- Deligne's complex archimedean factor `Gammaℂ` does not vanish off the real axis. -/
theorem Gammaℂ_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Gammaℂ z ≠ 0 := by
  rw [Ne, Gammaℂ_eq_zero_iff]
  rintro ⟨n, hn⟩
  exact hz (by simp [hn])

/-- `Gammaℝ` is complex-differentiable wherever its total value is nonzero. -/
theorem differentiableAt_Gammaℝ {z : ℂ} (hz : Gammaℝ z ≠ 0) : DifferentiableAt ℂ Gammaℝ z := by
  simpa only [inv_inv] using (differentiable_Gammaℝ_inv z).fun_inv (inv_ne_zero hz)

/-- `Gammaℂ` is complex-differentiable wherever its total value is nonzero. -/
theorem differentiableAt_Gammaℂ {z : ℂ} (hz : Gammaℂ z ≠ 0) : DifferentiableAt ℂ Gammaℂ z := by
  simpa only [inv_inv] using (differentiable_Gammaℂ_inv z).fun_inv (inv_ne_zero hz)

/-- `Gammaℝ` is continuous wherever its total value is nonzero. -/
theorem continuousAt_Gammaℝ {z : ℂ} (hz : Gammaℝ z ≠ 0) : ContinuousAt Gammaℝ z :=
  (differentiableAt_Gammaℝ hz).continuousAt

/-- `Gammaℂ` is continuous wherever its total value is nonzero. -/
theorem continuousAt_Gammaℂ {z : ℂ} (hz : Gammaℂ z ≠ 0) : ContinuousAt Gammaℂ z :=
  (differentiableAt_Gammaℂ hz).continuousAt

/-- Norm of Deligne's real archimedean factor: `‖Γ_ℝ(z)‖ = π ^ (-z.re / 2) ‖Γ(z / 2)‖`, including
at the poles where both sides are zero. -/
theorem norm_Gammaℝ (z : ℂ) : ‖Gammaℝ z‖ = Real.pi ^ (-z.re / 2) * ‖Gamma (z / 2)‖ := by
  rw [Gammaℝ_def, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  simp [neg_div]

/-- Norm of Deligne's complex archimedean factor: `‖Γ_ℂ(z)‖ = 2 (2π) ^ (-z.re) ‖Γ(z)‖`, including
at the poles where both sides are zero. -/
theorem norm_Gammaℂ (z : ℂ) : ‖Gammaℂ z‖ = 2 * (2 * Real.pi) ^ (-z.re) * ‖Gamma z‖ := by
  have h2pi : (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [Gammaℂ_def, h2pi, norm_mul, norm_mul, norm_ofNat,
    norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re]

/-- Logarithm of the norm of `Gammaℝ` away from its poles:
`log ‖Γ_ℝ(z)‖ = -(z.re / 2) log π + log ‖Γ(z / 2)‖`. -/
theorem log_norm_Gammaℝ {z : ℂ} (hz : Gammaℝ z ≠ 0) :
    Real.log ‖Gammaℝ z‖ = -(z.re / 2) * Real.log Real.pi + Real.log ‖Gamma (z / 2)‖ := by
  have hpow : 0 < Real.pi ^ (-z.re / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hΓ : ‖Gamma (z / 2)‖ ≠ 0 := by
    intro h0
    apply hz
    rw [← norm_eq_zero, norm_Gammaℝ, h0, mul_zero]
  rw [norm_Gammaℝ, Real.log_mul hpow.ne' hΓ, Real.log_rpow Real.pi_pos, neg_div]

/-- Logarithm of the norm of `Gammaℂ` away from its poles:
`log ‖Γ_ℂ(z)‖ = log 2 - z.re log (2π) + log ‖Γ(z)‖`. -/
theorem log_norm_Gammaℂ {z : ℂ} (hz : Gammaℂ z ≠ 0) :
    Real.log ‖Gammaℂ z‖ =
      Real.log 2 - z.re * Real.log (2 * Real.pi) + Real.log ‖Gamma z‖ := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  have hpow : 0 < (2 * Real.pi) ^ (-z.re) := Real.rpow_pos_of_pos h2pi _
  have hΓ : ‖Gamma z‖ ≠ 0 := by
    intro h0
    apply hz
    rw [← norm_eq_zero, norm_Gammaℂ, h0, mul_zero]
  rw [norm_Gammaℂ, Real.log_mul (by positivity) hΓ, Real.log_mul two_ne_zero hpow.ne',
    Real.log_rpow h2pi]
  ring

end Complex

