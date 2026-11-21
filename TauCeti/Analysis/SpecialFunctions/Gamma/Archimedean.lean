/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Zero locus, relations, regularity, norms, and integer values of the archimedean gamma factors

Deligne's archimedean factors are
$$\Gamma_{\mathbb{R}}(s) = \pi^{-s/2} \Gamma(s/2), \qquad
  \Gamma_{\mathbb{C}}(s) = 2 (2\pi)^{-s} \Gamma(s).$$
Mathlib uses total division for the gamma function, so `Gammaℝ` and `Gammaℂ` take the junk value
`0` at their poles `-2n` and `-n` (`n : ℕ`) and are nonzero everywhere else; in particular neither
vanishes off the real axis. Because their reciprocals are entire (`differentiable_Gammaℝ_inv` and
`differentiable_Gammaℂ_inv`), both factors are analytic wherever they are nonzero.

Since the bases `π` and `2π` are positive reals, their complex powers have norms `π ^ (-s.re / 2)`
and `(2π) ^ (-s.re)`. Taking norms and real logarithms separates those exponential prefactors from
`‖Γ(s / 2)‖` and `‖Γ(s)‖`, preparing the vertical-strip Stirling asymptotics of `Gammaℝ`,
`Gammaℂ`, and finite products of shifted factors.

## Main declarations

* `Complex.analyticAt_Gammaℝ_of_ne_zero`, `Complex.analyticAt_Gammaℂ_of_ne_zero`: both factors
  are analytic wherever they are nonzero.
* `Complex.Gammaℂ_eq_zero_iff`: total zeros of `Gammaℂ` occur at `-(n : ℂ)` (`n : ℕ`),
  complementing `Complex.Gammaℝ_eq_zero_iff`; this identifies the exceptional values in finite
  products of shifted gamma factors.
* `Complex.two_mul_Gammaℝ_two_mul`: twice the real factor at `2 * z` is `2 ^ z` times `Gammaℂ z`,
  everywhere on `ℂ` including at the poles where both totalized values vanish.
* `Complex.Gammaℂ_ne_zero_of_re_pos`, `Complex.Gammaℝ_ne_zero_of_im_ne_zero`,
  `Complex.Gammaℂ_ne_zero_of_im_ne_zero`: nonvanishing on the right half-plane and off the real
  axis.
* `Complex.differentiableAt_Gammaℝ`, `Complex.differentiableAt_Gammaℂ`,
  `Complex.continuousAt_Gammaℝ`, `Complex.continuousAt_Gammaℂ`: regularity away from the poles.
* `Complex.norm_Gammaℝ`, `Complex.norm_Gammaℂ`, `Complex.log_norm_Gammaℝ`,
  `Complex.log_norm_Gammaℂ`: norm and log-norm identities.
* `Complex.Gammaℂ_nat_add_one`, `Complex.Gammaℝ_two_mul_nat_add_two`,
  `Complex.Gammaℝ_two_mul_nat_add_one`, `Complex.Gammaℝ_neg_two_mul_nat_sub_one`: the values at
  positive integers and at the negative odd integers, where `Gammaℝ` is regular; each is a
  rational multiple of a power of `π`.

## References

* P. Deligne, *Valeurs de fonctions L et périodes d'intégrales*, Proc. Symp. Pure Math. 33 (1979),
  Part 2, §5.3.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory* (2004), §5.1.
-/

public section

namespace Complex

/-- The real-place gamma factor is analytic wherever it is nonzero. -/
@[fun_prop]
theorem analyticAt_Gammaℝ_of_ne_zero {s : ℂ} (hs : Gammaℝ s ≠ 0) :
    AnalyticAt ℂ Gammaℝ s := by
  simpa only [Pi.inv_def, inv_inv] using
    (differentiable_Gammaℝ_inv.analyticAt s).inv (inv_ne_zero hs)

/-- The complex-place gamma factor is analytic wherever it is nonzero. -/
@[fun_prop]
theorem analyticAt_Gammaℂ_of_ne_zero {s : ℂ} (hs : Gammaℂ s ≠ 0) :
    AnalyticAt ℂ Gammaℂ s := by
  simpa only [Pi.inv_def, inv_inv] using
    (differentiable_Gammaℂ_inv.analyticAt s).inv (inv_ne_zero hs)

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

/-- Deligne's complex archimedean factor `Gammaℂ` is nonzero on the open right half-plane. -/
theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (by simp [Real.pi_ne_zero]))
    (Gamma_ne_zero_of_re_pos hs)

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
@[fun_prop]
theorem differentiableAt_Gammaℝ {z : ℂ} (hz : Gammaℝ z ≠ 0) : DifferentiableAt ℂ Gammaℝ z := by
  simpa only [inv_inv] using (differentiable_Gammaℝ_inv z).fun_inv (inv_ne_zero hz)

/-- `Gammaℂ` is complex-differentiable wherever its total value is nonzero. -/
@[fun_prop]
theorem differentiableAt_Gammaℂ {z : ℂ} (hz : Gammaℂ z ≠ 0) : DifferentiableAt ℂ Gammaℂ z := by
  simpa only [inv_inv] using (differentiable_Gammaℂ_inv z).fun_inv (inv_ne_zero hz)

/-- `Gammaℝ` is continuous wherever its total value is nonzero. -/
@[fun_prop]
theorem continuousAt_Gammaℝ {z : ℂ} (hz : Gammaℝ z ≠ 0) : ContinuousAt Gammaℝ z :=
  (differentiableAt_Gammaℝ hz).continuousAt

/-- `Gammaℂ` is continuous wherever its total value is nonzero. -/
@[fun_prop]
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

section IntegerValues

open scoped Nat

/-- The complex archimedean factor at a positive integer: `Γ_ℂ(m + 1) = 2 m! / (2π) ^ (m + 1)`. -/
theorem Gammaℂ_nat_add_one (m : ℕ) :
    Gammaℂ (m + 1) = 2 * m ! / (2 * Real.pi) ^ (m + 1) := by
  rw [Gammaℂ_def, Gamma_nat_eq_factorial,
    show -((m : ℂ) + 1) = -((m + 1 : ℕ) : ℂ) by push_cast; ring, cpow_neg, cpow_natCast]
  ring

/-- The real archimedean factor at a positive even integer: `Γ_ℝ(2k + 2) = k! / π ^ (k + 1)`. -/
theorem Gammaℝ_two_mul_nat_add_two (k : ℕ) :
    Gammaℝ (2 * k + 2) = k ! / Real.pi ^ (k + 1) := by
  rw [Gammaℝ_def, show -(2 * (k : ℂ) + 2) / 2 = -((k + 1 : ℕ) : ℂ) by push_cast; ring,
    show (2 * (k : ℂ) + 2) / 2 = k + 1 by ring, Gamma_nat_eq_factorial, cpow_neg, cpow_natCast]
  ring

/-- The real archimedean factor at a positive odd integer:
`Γ_ℝ(2k + 1) = (2k)! / (4 ^ k k! π ^ k)`. -/
theorem Gammaℝ_two_mul_nat_add_one (k : ℕ) :
    Gammaℝ (2 * k + 1) = (2 * k)! / (4 ^ k * k ! * Real.pi ^ k) := by
  -- Legendre duplication `Γ_ℝ(s) Γ_ℝ(s + 1) = Γ_ℂ(s)` at `s = 2k + 1`, and the two values above
  have h := Gammaℝ_mul_Gammaℝ_add_one (2 * k + 1)
  rw [show 2 * (k : ℂ) + 1 + 1 = 2 * k + 2 by ring, Gammaℝ_two_mul_nat_add_two,
    show 2 * (k : ℂ) + 1 = ((2 * k : ℕ) : ℂ) + 1 by push_cast; ring, Gammaℂ_nat_add_one] at h
  rw [show 2 * (k : ℂ) + 1 = ((2 * k : ℕ) : ℂ) + 1 by push_cast; ring]
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have h4 : (4 : ℂ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  rw [eq_div_iff (by simp [hπ, hk]), h4]
  field_simp at h
  refine mul_left_cancel₀ (by simp [hπ] : (2 * Real.pi ^ (k + 1) : ℂ) ≠ 0) ?_
  linear_combination h

/-- The real archimedean factor at a negative odd integer, where it is regular:
`Γ_ℝ(-2k - 1) = (-1) ^ (k + 1) 4 ^ (k + 1) (k + 1)! π ^ (k + 1) / (2k + 2)!`. -/
theorem Gammaℝ_neg_two_mul_nat_sub_one (k : ℕ) :
    Gammaℝ (-(2 * k) - 1) =
      (-1) ^ (k + 1) * 4 ^ (k + 1) * (k + 1)! * Real.pi ^ (k + 1) / (2 * k + 2)! := by
  -- the reflection formula `Γ_ℝ(1 - s) Γ_ℝ(1 + s) = 1 / cos (π s / 2)` at `s = 2k + 2`
  have h := Gammaℝ_one_sub_mul_Gammaℝ_one_add (2 * k + 2)
  have hcos : cos (((k + 1 : ℕ) : ℂ) * Real.pi) = (-1) ^ (k + 1) := by
    rw [← ofReal_natCast, ← ofReal_mul, ← ofReal_cos, Real.cos_nat_mul_pi]
    push_cast; ring
  rw [show 1 - (2 * (k : ℂ) + 2) = -(2 * k) - 1 by ring,
    show 1 + (2 * (k : ℂ) + 2) = 2 * ((k + 1 : ℕ) : ℂ) + 1 by push_cast; ring,
    Gammaℝ_two_mul_nat_add_one,
    show (Real.pi : ℂ) * (2 * k + 2) / 2 = ((k + 1 : ℕ) : ℂ) * Real.pi by push_cast; ring, hcos,
    ← inv_pow, inv_neg, inv_one,
    show 2 * (k + 1) = 2 * k + 2 by ring] at h
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk : ((k + 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (k + 1).factorial_ne_zero
  rw [eq_div_iff (Nat.cast_ne_zero.mpr (2 * k + 2).factorial_ne_zero)]
  field_simp at h
  linear_combination h

end IntegerValues

end Complex

