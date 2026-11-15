/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Mellin transforms of dilations and decaying exponentials, and congruence on `(0, ∞)`

`HasMellin.comp_mul_right` transports a convergent Mellin transform under a positive dilation,
combining Mathlib's `MellinConvergent.comp_mul_left` and `mellin_comp_mul_right`.

For `c > 0` the Mellin transform of `t ↦ e^(-c t)` converges on `0 < Re z`
(`TauCeti.mellinConvergent_exp_neg_mul`). At `c = 1` this is the convergence of Euler's integral
for `Γ(z)` (`Complex.GammaIntegral_convergent`), and the scaling `t ↦ c t` is Mathlib's
`MellinConvergent.comp_mul_left`. Its value `c^(-z) Γ(z)` is Mathlib's
`Complex.integral_cpow_mul_exp_neg_mul_Ioi`. Against the multiplicative Haar measure `dt / t`
(`TauCeti.multHaar`), this gives the integrability and evaluation
`∫ t^(z / 2) e^(-π a² t) dt / t = Γ_ℝ(z) a^(-z)` for `0 < a` and `0 < Re z`
(`TauCeti.integrable_cpow_div_two_mul_exp_neg_multHaar`,
`TauCeti.integral_cpow_div_two_mul_exp_neg_multHaar`), the one-place gamma integrals produced by
Gaussians `e^(-π a² t)` in Hecke's integral representations of zeta and L-functions.

The Mellin transform reads a function only on `(0, ∞)`, so functions agreeing there have the same
transform, with the same convergence (`TauCeti.hasMellin_congr`). Kernels that are extended by zero
off `(0, ∞)` are compared with their unextended forms this way.
-/

public section

open Complex MeasureTheory Set
open scoped Real

namespace TauCeti

/-- Functions that agree on `(0, ∞)` have the same Mellin transform, with the same convergence. -/
theorem hasMellin_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℝ → E}
    (h : EqOn f g (Ioi 0)) {s : ℂ} {m : E} : HasMellin f s m ↔ HasMellin g s m := by
  have h' : EqOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • f t) (fun t ↦ (t : ℂ) ^ (s - 1) • g t)
      (Ioi 0) := fun t ht ↦ by simp only [h ht]
  simp only [HasMellin, MellinConvergent, mellin,
    MeasureTheory.integrableOn_congr_fun h' measurableSet_Ioi,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h']

/-- For `c > 0` the Mellin transform of `t ↦ e^(-c t)` converges on `0 < Re z`. -/
theorem mellinConvergent_exp_neg_mul {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : 0 < z.re) :
    MellinConvergent (fun t : ℝ ↦ (Real.exp (-(c * t)) : ℂ)) z := by
  refine (MellinConvergent.comp_mul_left (f := fun t : ℝ ↦ (Real.exp (-t) : ℂ)) hc).mpr ?_
  exact (GammaIntegral_convergent hz).congr_fun (fun t _ ↦ mul_comm _ _) measurableSet_Ioi

/-- The Gaussian `t ↦ exp (-π a² t)` (`0 < a`) is integrable against `t ^ (z / 2) dt / t` whenever
`0 < z.re`. -/
theorem integrable_cpow_div_two_mul_exp_neg_multHaar {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 0 < z.re) :
    Integrable (fun t : ℝ ↦ (t : ℂ) ^ (z / 2) * (Real.exp (-(π * a ^ 2 * t)) : ℂ))
      multHaar := by
  have hz2 : 0 < (z / 2).re := by
    rw [div_ofNat_re]
    exact half_pos hz
  simpa only [smul_eq_mul] using integrable_multHaar_cpow_smul_iff.mpr
    (mellinConvergent_exp_neg_mul (by positivity) hz2)

/-- The Mellin integral of `t ↦ exp (-π a² t)` against `t ^ (z / 2) dt / t`, for `0 < a` and
`0 < z.re`: `∫ t^(z / 2) e^(-π a² t) dt / t = Γ_ℝ(z) a^(-z)`. -/
theorem integral_cpow_div_two_mul_exp_neg_multHaar {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 0 < z.re) :
    ∫ t, (t : ℂ) ^ (z / 2) * (Real.exp (-(π * a ^ 2 * t)) : ℂ) ∂multHaar =
      Gammaℝ z * (a : ℂ) ^ (-z) := by
  have hz2 : 0 < (z / 2).re := by
    rw [div_ofNat_re]
    exact half_pos hz
  have hc : 0 < π * a ^ 2 := by positivity
  have hpow : ((π * a ^ 2 : ℝ) : ℂ) ^ (-(z / 2)) = (π : ℂ) ^ (-z / 2) * (a : ℂ) ^ (-z) := by
    rw [ofReal_mul, ofReal_mul_cpow Real.pi_pos.le, ofReal_pow, ofReal_pow_cpow ha.le]
    congr 2 <;> ring
  have h := integral_multHaar_cpow_smul (fun t : ℝ ↦ (Real.exp (-(π * a ^ 2 * t)) : ℂ)) (z / 2)
  simp only [smul_eq_mul, mellin, ofReal_exp, ofReal_neg, ofReal_mul (π * a ^ 2)] at h ⊢
  rw [h, integral_cpow_mul_exp_neg_mul_Ioi hz2 hc, one_div, inv_cpow_ofReal_nonneg hc.le,
    ← cpow_neg, hpow, Gammaℝ_def]
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
