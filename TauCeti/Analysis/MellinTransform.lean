/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Mellin transforms of dilations, exponentials, and a continuous cutoff

`HasMellin.comp_mul_right` transports a convergent Mellin transform under a positive dilation,
combining Mathlib's `MellinConvergent.comp_mul_left` and `mellin_comp_mul_right`.

For `c > 0` the Mellin transform of `t ↦ e^(-c t)` converges on `0 < Re z`
(`TauCeti.mellinConvergent_exp_neg_mul`). At `c = 1` this is the convergence of Euler's integral
for `Γ(z)` (`Complex.GammaIntegral_convergent`), and the scaling `t ↦ c t` is Mathlib's
`MellinConvergent.comp_mul_left`. Its value `c^(-z) Γ(z)` is Mathlib's
`Complex.integral_cpow_mul_exp_neg_mul_Ioi`; at `c = 1` it is `Γ(z)`
(`TauCeti.hasMellin_exp_neg`). Written against the multiplicative Haar measure
`dt / t` (`TauCeti.multHaar`), these give integrability and evaluation of `t ^ z e^(-c t)`
(`TauCeti.integrable_multHaar_cpow_mul_exp_neg_mul`,
`TauCeti.integral_multHaar_cpow_mul_exp_neg_mul`) and their `Γ_ℝ` specialization for
`t ^ (z / 2) e^(-π a² t)` (`TauCeti.integrable_multHaar_cpow_div_two_mul_exp_neg_pi_mul_sq`,
`TauCeti.integral_multHaar_cpow_div_two_mul_exp_neg_pi_mul_sq`), which are the one-place gamma
integrals produced by Gaussians in Hecke's integral representations of zeta and L-functions.

`TauCeti.hasMellin_max_one_sub_zero` computes the Mellin transform of the continuous cutoff
`max (1 - t) 0`, using the difference of Mathlib's interval-power transforms. Its inverse
transform gives the first-order Perron weight.
-/

public section

open Complex MeasureTheory Set
open scoped Real

namespace TauCeti

/-- The Mellin transform of the continuous cutoff `max (1 - t) 0` is `1 / (s(s+1))`
for `0 < Re s`. Only its values on `(0, ∞)` contribute to the transform. -/
theorem hasMellin_max_one_sub_zero {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun t : ℝ ↦ ((max (1 - t) 0 : ℝ) : ℂ)) s ((s * (s + 1))⁻¹) := by
  have h0 := hasMellin_one_Ioc hs
  have h1 := hasMellin_cpow_Ioc (1 : ℂ) (by simpa using (by linarith : 0 < s.re + 1))
  have hh := hasMellin_sub h0.1 h1.1
  rw [h0.2, h1.2] at hh
  refine (hasMellin_congr (f := fun t ↦
    (Ioc (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℂ)) t -
      (Ioc (0 : ℝ) 1).indicator (fun u ↦ (u : ℂ) ^ (1 : ℂ)) t) ?_).mp ?_
  · intro t ht
    have ht0 : 0 < t := Set.mem_Ioi.mp ht
    by_cases h : t ≤ 1
    · simp [ht0, h]
    · have ht1 : 1 - t ≤ 0 := by linarith
      simp [h, max_eq_right ht1]
  · have hs0 : s ≠ 0 := by intro h; simp [h] at hs
    have hs1 : s + 1 ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    refine ⟨hh.1, hh.2.trans ?_⟩
    field_simp [hs0, hs1]
    ring

/-- For `c > 0` the Mellin transform of `t ↦ e^(-c t)` converges on `0 < Re z`. -/
theorem mellinConvergent_exp_neg_mul {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.re) :
    MellinConvergent (fun t : ℝ ↦ (Real.exp (-(c * t)) : ℂ)) z := by
  refine (MellinConvergent.comp_mul_left (f := fun t : ℝ ↦ (Real.exp (-t) : ℂ)) hc).mpr ?_
  exact (GammaIntegral_convergent hz).congr_fun (fun t _ ↦ mul_comm _ _) measurableSet_Ioi

/-- Euler's integral as a Mellin transform: on `0 < Re z` the Mellin transform of `t ↦ e^(-t)`
converges and equals `Γ(z)`. -/
theorem hasMellin_exp_neg {z : ℂ} (hz : 0 < z.re) :
    HasMellin (fun t : ℝ ↦ (Real.exp (-t) : ℂ)) z (Gamma z) :=
  ⟨(GammaIntegral_convergent hz).congr_fun (fun t _ ↦ mul_comm _ _) measurableSet_Ioi,
    by rw [← GammaIntegral_eq_mellin, Gamma_eq_integral hz]⟩

/-- For `c > 0` and `0 < Re z`, `t ↦ t ^ z * exp (-c t)` is integrable against `dt / t`. -/
theorem integrable_multHaar_cpow_mul_exp_neg_mul {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun t : ℝ ↦ (t : ℂ) ^ z * (Real.exp (-(c * t)) : ℂ)) multHaar := by
  simpa only [smul_eq_mul] using integrable_multHaar_cpow_smul_iff.mpr
    (mellinConvergent_exp_neg_mul hc hz)

/-- For `c ≥ 0` and `0 < Re z`, `∫ t ^ z exp (-c t) dt / t = c ^ (-z) * Γ(z)`. When `c = 0`,
`t ↦ t ^ z` is not integrable against `dt / t` and both sides vanish. -/
theorem integral_multHaar_cpow_mul_exp_neg_mul {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : 0 < z.re) :
    ∫ t : ℝ, (t : ℂ) ^ z * (Real.exp (-(c * t)) : ℂ) ∂multHaar =
      (c : ℂ) ^ (-z) * Gamma z := by
  rcases hc.eq_or_lt with rfl | hc'
  · have hz0 : -z ≠ 0 := neg_ne_zero.mpr fun h ↦ by simp [h] at hz
    simp [integral_multHaar_cpow_eq_zero, zero_cpow hz0]
  · have h := integral_multHaar_cpow_smul (fun t : ℝ ↦ (Real.exp (-(c * t)) : ℂ)) z
    simp only [smul_eq_mul, mellin, ofReal_exp, ofReal_neg, ofReal_mul c] at h ⊢
    rw [h, integral_cpow_mul_exp_neg_mul_Ioi hz hc', one_div, inv_cpow_ofReal_nonneg hc'.le,
      ← cpow_neg]

/-- For `a ≠ 0` and `0 < Re z`, `t ↦ t ^ (z / 2) * exp (-π a² t)` is integrable against `dt / t`. -/
theorem integrable_multHaar_cpow_div_two_mul_exp_neg_pi_mul_sq {a : ℝ} (ha : a ≠ 0) {z : ℂ}
    (hz : 0 < z.re) :
    Integrable (fun t : ℝ ↦ (t : ℂ) ^ (z / 2) * (Real.exp (-(π * a ^ 2 * t)) : ℂ)) multHaar :=
  integrable_multHaar_cpow_mul_exp_neg_mul (by positivity) (by rw [div_ofNat_re]; exact half_pos hz)

/-- For `a : ℝ` and `0 < Re z`, `∫ t ^ (z / 2) exp (-π a² t) dt / t = Γ_ℝ(z) * |a| ^ (-z)`.
When `a = 0`, `t ↦ t ^ (z / 2)` is not integrable against `dt / t` and both sides vanish. -/
theorem integral_multHaar_cpow_div_two_mul_exp_neg_pi_mul_sq (a : ℝ) {z : ℂ} (hz : 0 < z.re) :
    ∫ t : ℝ, (t : ℂ) ^ (z / 2) * (Real.exp (-(π * a ^ 2 * t)) : ℂ) ∂multHaar =
      Gammaℝ z * ((|a| : ℝ) : ℂ) ^ (-z) := by
  have hz2 : 0 < (z / 2).re := by rw [div_ofNat_re]; exact half_pos hz
  rw [integral_multHaar_cpow_mul_exp_neg_mul (by positivity) hz2, ← sq_abs a, ofReal_mul,
    ofReal_mul_cpow Real.pi_pos.le, ofReal_pow, ofReal_pow_cpow (abs_nonneg a), Gammaℝ_def,
    neg_div, Nat.cast_ofNat, mul_neg, mul_div_cancel₀ _ two_ne_zero]
  ring

end TauCeti

namespace HasMellin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Dilation of the Mellin variable preserves convergence and multiplies the transform by
`a^(-s)`. -/
theorem comp_mul_right {f : ℝ → E} {s : ℂ} {m : E} (h : HasMellin f s m)
    {a : ℝ} (ha : 0 < a) : HasMellin (fun t ↦ f (t * a)) s ((a : ℂ) ^ (-s) • m) := by
  constructor
  · simpa only [mul_comm] using (MellinConvergent.comp_mul_left (f := f) (s := s) ha).mpr h.1
  · rw [mellin_comp_mul_right f s ha, h.2]

end HasMellin
