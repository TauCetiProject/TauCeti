/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Stable.CompensatedIntegral
public import TauCeti.Probability.Distributions.Stable.Exponent
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.MeasureTheory.Integral.RpowLaplace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Lévy–Khintchine formula for stable exponents

For `0 < α < 2` and `|β| ≤ 1`, let `ν` be the stable Lévy measure `stableLevyMeasure α β`, with
density `Γ(1 + α) sin(πα/2) / π * ((1 + β) 1_{x > 0} + (1 - β) 1_{x < 0}) |x| ^ (-1 - α)`.
This file proves that for every real `t`,

`∫ x, exp (i t x) - 1 - i t sin x ∂ν = stableCharacteristicExponent α β t`,

so the sine-compensated Lévy integral is exactly the stable characteristic exponent `Ψ_{α,β}`
in Nolan's `S₀` parameterization, including the logarithmic branch at `α = 1` and both
full-skewness boundaries. Combined with the compensated compound-Poisson approximations, this
identifies the limit of their characteristic functions as `exp (Ψ_{α,β} t)`.

## Proof

Reflection reduces the integral to the positive half-line, where the weight `x ^ (-(α + 1))`
is written as a Gamma mixture of exponentials (`TauCeti.integral_Ioi_rpow_neg_smul`). The
Laplace transform of the compensated kernel is the rational function
`(s - i t)⁻¹ - s⁻¹ - i t / (1 + s ^ 2)`, and the remaining power-weighted integrals reduce to
`∫ y in Ioi 0, y ^ (s - 1) / (y ^ 2 + t ^ 2)`, evaluated by Euler's reflection formula
(`TauCeti.integral_rpow_div_sq_add_sq`). The imaginary part needs three cases: below and above
shape one the integrand splits into two such integrals, and at shape one it has an elementary
logarithmic primitive.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
* K. Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge University Press,
  1999, section 14.
-/

public section

noncomputable section

open MeasureTheory Real Set Filter
open scoped Topology

namespace TauCeti.Probability

/-- The Laplace transform of the compensated kernel on the positive half-line. -/
private lemma integral_exp_neg_mul_smul_kernel {s : ℝ} (hs : 0 < s) (t : ℝ) :
    ∫ x in Ioi (0 : ℝ), exp (-(x * s)) • (Complex.exp ((t * x : ℝ) * Complex.I) - 1 -
      (t * sin x : ℝ) * Complex.I) =
      ((s / (s ^ 2 + t ^ 2) - s⁻¹ : ℝ) : ℂ) +
        ((t / (s ^ 2 + t ^ 2) - t / (1 + s ^ 2) : ℝ) : ℂ) * Complex.I := by
  have hI (a : ℂ) (ha : a.re < 0) : ∫ x in Ioi (0 : ℝ), Complex.exp (a * x) = -1 / a := by
    simpa using integral_exp_mul_complex_Ioi ha 0
  have hint (a : ℂ) (ha : a.re < 0) :
      IntegrableOn (fun x : ℝ ↦ Complex.exp (a * x)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi ha 0
  have h1 : (-s + t * Complex.I : ℂ).re < 0 := by simpa using hs
  have h2 : (-s : ℂ).re < 0 := by simpa using hs
  have h3 : (-s + Complex.I : ℂ).re < 0 := by simpa using hs
  have h4 : (-s - Complex.I : ℂ).re < 0 := by simpa using hs
  calc
    _ = ∫ x in Ioi (0 : ℝ), (Complex.exp ((-s + t * Complex.I) * x) -
          Complex.exp ((-s : ℂ) * x)) - (t / 2 : ℂ) * (Complex.exp ((-s + Complex.I) * x) -
          Complex.exp ((-s - Complex.I) * x)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
      simp only [Complex.real_smul, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
        Complex.ofReal_sin, Complex.sin, add_mul, sub_mul, neg_mul, Complex.exp_add,
        Complex.exp_sub, Complex.exp_neg]
      ring_nf
      simp only [Complex.I_sq]
      ring
    _ = _ := by
      rw [integral_sub ((hint _ h1).sub' (hint _ h2)) (((hint _ h3).sub' (hint _ h4)).const_mul _),
        integral_sub (hint _ h1) (hint _ h2), integral_const_mul,
        integral_sub (hint _ h3) (hint _ h4), hI _ h1, hI _ h2, hI _ h3, hI _ h4]
      have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      have hst : (s : ℂ) ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
        exact_mod_cast (by positivity : s ^ 2 + t ^ 2 ≠ 0)
      have hs1 : 1 + (s : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (by positivity : 1 + s ^ 2 ≠ 0)
      have e1 : (-s + t * Complex.I : ℂ) ≠ 0 := by
        intro h; simpa [hs.ne'] using congrArg Complex.re h
      have e3 : (-s + Complex.I : ℂ) ≠ 0 := by
        intro h; simpa [hs.ne'] using congrArg Complex.re h
      have e4 : (-s - Complex.I : ℂ) ≠ 0 := by
        intro h; simpa [hs.ne'] using congrArg Complex.re h
      push_cast
      field_simp
      ring_nf
      simp only [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
      ring

/-- The real part of the power-weighted Laplace transform of the compensated kernel. -/
private lemma integral_rpow_mul_re {α : ℝ} (hα : 0 < α) (hα2 : α < 2) (t : ℝ) :
    ∫ s in Ioi (0 : ℝ), s ^ α * (s / (s ^ 2 + t ^ 2) - s⁻¹) =
      -|t| ^ α * (π / (2 * sin (π * α / 2))) := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [abs_zero, zero_rpow hα.ne', neg_zero, zero_mul,
      setIntegral_congr_fun measurableSet_Ioi (g := fun _ ↦ (0 : ℝ)) fun s (hs : 0 < s) ↦ by
        simp only
        field_simp
        ring]
    exact integral_zero _ _
  have ht' := abs_pos.mpr ht
  calc
    _ = ∫ s in Ioi (0 : ℝ), (-t ^ 2) * (s ^ (α - 1) / (s ^ 2 + t ^ 2)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
      rw [rpow_sub_one hs.ne']
      field_simp
      ring
    _ = _ := by
      rw [integral_const_mul, integral_rpow_div_sq_add_sq hα hα2 ht, ← sq_abs t,
        rpow_sub ht', rpow_two]
      field_simp

/-- The imaginary part of the power-weighted Laplace transform below shape one. -/
private lemma integral_rpow_mul_im_of_lt_one {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (t : ℝ) :
    ∫ s in Ioi (0 : ℝ), s ^ α * (t / (s ^ 2 + t ^ 2) - t / (1 + s ^ 2)) =
      (t * |t| ^ (α - 1) - t) * (π / (2 * cos (π * α / 2))) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have h0 : 0 < α + 1 := by linarith
  have h2 : α + 1 < 2 := by linarith
  have hsin : sin (π * (α + 1) / 2) = cos (π * α / 2) := by
    rw [show π * (α + 1) / 2 = π * α / 2 + π / 2 by ring, sin_add_pi_div_two]
  calc
    _ = ∫ s in Ioi (0 : ℝ), (t * (s ^ (α + 1 - 1) / (s ^ 2 + t ^ 2)) -
          t * (s ^ (α + 1 - 1) / (s ^ 2 + 1 ^ 2))) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun s _ ↦ ?_
      rw [add_sub_cancel_right, one_pow, add_comm (s ^ 2) 1]
      ring
    _ = _ := by
      rw [integral_sub ((integrableOn_rpow_div_sq_add_sq h0 h2 ht).const_mul t)
        ((integrableOn_rpow_div_sq_add_sq h0 h2 one_ne_zero).const_mul t),
        integral_const_mul, integral_const_mul, integral_rpow_div_sq_add_sq h0 h2 ht,
        integral_rpow_div_sq_add_sq h0 h2 one_ne_zero, abs_one, one_rpow, hsin,
        show α + 1 - 2 = α - 1 by ring]
      ring

/-- The imaginary part of the power-weighted Laplace transform above shape one. -/
private lemma integral_rpow_mul_im_of_one_lt {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) (t : ℝ) :
    ∫ s in Ioi (0 : ℝ), s ^ α * (t / (s ^ 2 + t ^ 2) - t / (1 + s ^ 2)) =
      (t * |t| ^ (α - 1) - t) * (π / (2 * cos (π * α / 2))) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have h0 : 0 < α - 1 := by linarith
  have h2 : α - 1 < 2 := by linarith
  have ht' := abs_pos.mpr ht
  have hsin : sin (π * (α - 1) / 2) = -cos (π * α / 2) := by
    rw [show π * (α - 1) / 2 = π * α / 2 - π / 2 by ring, sin_sub_pi_div_two]
  have hcos : cos (π * α / 2) ≠ 0 :=
    (cos_neg_of_pi_div_two_lt_of_lt (by nlinarith [pi_pos]) (by nlinarith [pi_pos])).ne
  calc
    _ = ∫ s in Ioi (0 : ℝ), (t * (s ^ (α - 1 - 1) / (s ^ 2 + 1 ^ 2)) -
          t ^ 3 * (s ^ (α - 1 - 1) / (s ^ 2 + t ^ 2))) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ ?_
      have hpow : s ^ α = s ^ (α - 1 - 1) * s ^ 2 := by
        rw [← rpow_natCast, ← rpow_add hs]
        congr 1
        push_cast
        ring
      rw [hpow, one_pow, add_comm (s ^ 2) 1]
      field_simp
      ring
    _ = _ := by
      rw [integral_sub ((integrableOn_rpow_div_sq_add_sq h0 h2 one_ne_zero).const_mul t)
        ((integrableOn_rpow_div_sq_add_sq h0 h2 ht).const_mul _),
        integral_const_mul, integral_const_mul, integral_rpow_div_sq_add_sq h0 h2 ht,
        integral_rpow_div_sq_add_sq h0 h2 one_ne_zero, abs_one, one_rpow, hsin]
      have key : t ^ 3 * |t| ^ (α - 1 - 2) = t * |t| ^ (α - 1) := by
        rw [show t ^ 3 = t * |t| ^ 2 by rw [sq_abs]; ring, rpow_sub ht' (α - 1), rpow_two]
        field_simp
      linear_combination (π / (2 * cos (π * α / 2))) * key

/-- The imaginary part of the power-weighted Laplace transform at shape one. -/
private lemma integral_mul_im_one (t : ℝ)
    (hint : IntegrableOn (fun s : ℝ ↦ s ^ (1 : ℝ) * (t / (s ^ 2 + t ^ 2) - t / (1 + s ^ 2)))
      (Ioi 0)) :
    ∫ s in Ioi (0 : ℝ), s ^ (1 : ℝ) * (t / (s ^ 2 + t ^ 2) - t / (1 + s ^ 2)) =
      -(t * log |t|) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  let F : ℝ → ℝ := fun s ↦ t / 2 * (log (s ^ 2 + t ^ 2) - log (1 + s ^ 2))
  have hpos (s : ℝ) : s ^ 2 + t ^ 2 ≠ 0 := by positivity
  have hpos' (s : ℝ) : 1 + s ^ 2 ≠ 0 := by positivity
  have hcont : ContinuousAt F 0 := by
    refine continuousAt_const.mul (ContinuousAt.sub ?_ ?_)
    · exact (by fun_prop : Continuous fun s : ℝ ↦ s ^ 2 + t ^ 2).continuousAt.log (hpos 0)
    · exact (by fun_prop : Continuous fun s : ℝ ↦ 1 + s ^ 2).continuousAt.log (hpos' 0)
  have hderiv (s : ℝ) (_ : s ∈ Ioi (0 : ℝ)) :
      HasDerivAt F (s ^ (1 : ℝ) * (t / (s ^ 2 + t ^ 2) - t / (1 + s ^ 2))) s := by
    have h1 := ((hasDerivAt_pow 2 s).add_const (t ^ 2)).log (hpos s)
    have h2 := ((hasDerivAt_pow 2 s).const_add 1).log (hpos' s)
    convert (h1.sub h2).const_mul (t / 2) using 1
    rw [rpow_one]
    field_simp
    ring
  have hlim : Tendsto F atTop (𝓝 (t / 2 * 0)) := by
    have h1 : Tendsto (fun s : ℝ ↦ 1 + s ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ (1 : ℝ) (tendsto_pow_atTop (α := ℝ) two_ne_zero)
    have h2 : Tendsto (fun s : ℝ ↦ 1 + (t ^ 2 - 1) / (1 + s ^ 2)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.div_atTop h1).const_add (1 : ℝ)
    have h3 := ((continuousAt_log one_ne_zero).tendsto.comp h2).const_mul (t / 2)
    rw [log_one] at h3
    refine h3.congr fun s ↦ ?_
    simp only [Function.comp_apply, F]
    rw [← log_div (hpos s) (hpos' s)]
    congr 2
    field_simp
    ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt hderiv hint hlim]
  simp only [F]
  rw [zero_pow two_ne_zero, zero_add, add_zero, log_one, sub_zero, ← sq_abs, log_pow]
  push_cast
  ring

/-- Away from shape one, the imaginary part of the totally skewed stable exponent. -/
private lemma im_stableCharacteristicExponent_one_of_ne_one {α : ℝ} (hα : α ≠ 1) (t : ℝ) :
    (stableCharacteristicExponent α 1 t).im = tan (π * α / 2) * (t * |t| ^ (α - 1) - t) := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have hsign : Real.sign t * |t| ^ α = t * |t| ^ (α - 1) := by
    rw [rpow_sub_one (abs_pos.mpr ht).ne']
    rcases ht.lt_or_gt with ht | ht
    · rw [Real.sign_of_neg ht, abs_of_neg ht]
      field_simp
    · rw [Real.sign_of_pos ht, abs_of_pos ht]
      field_simp
  simp only [stableCharacteristicExponent_of_ne_one_of_ne_zero hα _ ht, Complex.add_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re, hsign]
  ring

/-- The power-weighted Laplace transform of the compensated kernel is a multiple of the
totally skewed stable exponent. -/
private lemma integral_rpow_smul_laplace {α : ℝ} (hα : 0 < α) (hα2 : α < 2) (t : ℝ)
    (hint : IntegrableOn (fun s : ℝ ↦ s ^ α • (((s / (s ^ 2 + t ^ 2) - s⁻¹ : ℝ) : ℂ) +
      ((t / (s ^ 2 + t ^ 2) - t / (1 + s ^ 2) : ℝ) : ℂ) * Complex.I)) (Ioi 0)) :
    ∫ s in Ioi (0 : ℝ), s ^ α • (((s / (s ^ 2 + t ^ 2) - s⁻¹ : ℝ) : ℂ) +
      ((t / (s ^ 2 + t ^ 2) - t / (1 + s ^ 2) : ℝ) : ℂ) * Complex.I) =
      (π / (2 * sin (π * α / 2))) • stableCharacteristicExponent α 1 t := by
  have hsin : sin (π * α / 2) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])).ne'
  apply Complex.ext
  · rw [← RCLike.re_to_complex, ← integral_re hint]
    simp only [RCLike.re_to_complex, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.mul_im, mul_zero, sub_zero, zero_mul, add_zero, mul_one,
      stableCharacteristicExponent_re hα.ne']
    rw [integral_rpow_mul_re hα hα2 t]
    ring
  · rw [← RCLike.im_to_complex, ← integral_im hint]
    simp only [RCLike.im_to_complex, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.mul_im, mul_zero, sub_zero, zero_mul, add_zero, mul_one, zero_add]
    rcases lt_trichotomy α 1 with h1 | rfl | h1
    · rw [integral_rpow_mul_im_of_lt_one hα h1 t,
        im_stableCharacteristicExponent_one_of_ne_one h1.ne, tan_eq_sin_div_cos]
      have hcos : cos (π * α / 2) ≠ 0 :=
        (cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩).ne'
      rw [mul_comm π α] at hsin hcos ⊢
      field_simp
    · have hJ : IntegrableOn (fun s : ℝ ↦ s ^ (1 : ℝ) * (t / (s ^ 2 + t ^ 2) - t / (1 + s ^ 2)))
          (Ioi 0) := hint.im.congr (ae_of_all _ fun s ↦ by
            simp only [RCLike.im_to_complex, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
              Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
              Complex.mul_im, mul_zero, sub_zero, zero_mul, add_zero, mul_one, zero_add])
      rw [integral_mul_im_one t hJ, stableCharacteristicExponent_one, mul_one, sin_pi_div_two]
      simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re]
      field_simp
      ring
    · rw [integral_rpow_mul_im_of_one_lt h1 hα2 t,
        im_stableCharacteristicExponent_one_of_ne_one h1.ne', tan_eq_sin_div_cos]
      have hcos : cos (π * α / 2) ≠ 0 :=
        (cos_neg_of_pi_div_two_lt_of_lt (by nlinarith [pi_pos]) (by nlinarith [pi_pos])).ne
      rw [mul_comm π α] at hsin hcos ⊢
      field_simp

variable {α β : ℝ}

/-- The density of a stable Lévy measure turns integrable functions into Lebesgue-integrable
ones. -/
private lemma integrable_stableLevyDensity_smul_iff (α β : ℝ) {g : ℝ → ℂ} :
    Integrable g (stableLevyMeasure α β) ↔
      Integrable (fun x ↦ stableLevyDensity α β x • g x) := by
  have hd : Measurable (stableLevyDensity α β) :=
    measurable_stableLevyDensity.comp
      (measurable_const.prodMk measurable_id : Measurable (fun x : ℝ ↦ ((α, β), x)))
  rw [stableLevyMeasure_def, integrable_withDensity_iff_integrable_smul' hd.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (stableLevyDensity_nonneg _ _ _)]

/-- Integrals against a stable Lévy measure split into power-weighted integrals over the two
half-lines. -/
private lemma integral_stableLevyMeasure_eq (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) {g : ℝ → ℂ}
    (hg : Integrable g (stableLevyMeasure α β)) :
    ∫ x, g x ∂stableLevyMeasure α β =
      (Gamma (1 + α) * sin (π * α / 2) / π * (1 + β)) •
          (∫ x in Ioi (0 : ℝ), x ^ (-(α + 1)) • g x) +
        (Gamma (1 + α) * sin (π * α / 2) / π * (1 - β)) •
          ∫ x in Ioi (0 : ℝ), x ^ (-(α + 1)) • g (-x) := by
  have hd : Measurable (stableLevyDensity α β) :=
    measurable_stableLevyDensity.comp
      (measurable_const.prodMk measurable_id : Measurable (fun x : ℝ ↦ ((α, β), x)))
  have hint := (integrable_stableLevyDensity_smul_iff α β).mp hg
  rw [stableLevyMeasure_def, integral_withDensity_eq_integral_toReal_smul hd.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (stableLevyDensity_nonneg _ _ _)]
  have hIic := integral_comp_neg_Ioi 0 (fun x ↦ stableLevyDensity α β x • g x)
  rw [neg_zero] at hIic
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hint.integrableOn hint.integrableOn,
    ← hIic, add_comm, ← integral_smul, ← integral_smul]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
    rw [stableLevyDensity_of_ne_zero hα hβ hx.ne', ite_eq_left hx, abs_of_pos hx, smul_smul]
  · refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
    rw [stableLevyDensity_of_ne_zero hα hβ (neg_ne_zero.mpr hx.ne'),
      ite_eq_right (not_lt.mpr (neg_nonpos.mpr hx.le)), abs_neg, abs_of_pos hx, smul_smul]

/-- **The Lévy–Khintchine formula for stable exponents.** For `0 < α < 2` and `|β| ≤ 1`,
integrating the sine-compensated characteristic kernel against the stable Lévy measure gives
the stable characteristic exponent in Nolan's `S₀` parameterization. -/
theorem integral_exp_sub_one_sub_sin_stableLevyMeasure (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (t : ℝ) :
    ∫ x, Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * sin x : ℝ) * Complex.I
      ∂stableLevyMeasure α β = stableCharacteristicExponent α β t := by
  have hhalf (t : ℝ) : ∫ x in Ioi (0 : ℝ), x ^ (-(α + 1)) •
      (Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * sin x : ℝ) * Complex.I) =
      ((Gamma (α + 1))⁻¹ * (π / (2 * sin (π * α / 2)))) •
        stableCharacteristicExponent α 1 t := by
    have h0 := (integrable_stableLevyDensity_smul_iff α 0).mp
      (integrable_exp_sub_one_sub_sin_stableLevyMeasure α 0 t)
    have hc := stableLevyDensity_coefficient_pos hα
    have h0' : IntegrableOn (fun x : ℝ ↦ x ^ (-(α + 1)) •
        (Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * sin x : ℝ) * Complex.I)) (Ioi 0) := by
      refine IntegrableOn.congr_fun
        (Integrable.smul (Gamma (1 + α) * sin (π * α / 2) / π)⁻¹ h0.integrableOn)
        (fun x (hx : 0 < x) ↦ ?_) measurableSet_Ioi
      have hβ0 : |(0 : ℝ)| ≤ 1 := by simp
      rw [Pi.smul_apply, stableLevyDensity_of_ne_zero hα hβ0 hx.ne', ite_eq_left hx,
        abs_of_pos hx, add_zero, mul_one, smul_smul, inv_mul_cancel_left₀ hc.ne']
    have hα1 : -1 < α := by linarith [hα.1]
    have hint := integrableOn_rpow_smul_integral_exp_neg_mul_smul hα1 h0'
    have hL : EqOn (fun s : ℝ ↦ s ^ α • ∫ x in Ioi (0 : ℝ), exp (-(x * s)) •
        (Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * sin x : ℝ) * Complex.I))
        (fun s : ℝ ↦ s ^ α • (((s / (s ^ 2 + t ^ 2) - s⁻¹ : ℝ) : ℂ) +
          ((t / (s ^ 2 + t ^ 2) - t / (1 + s ^ 2) : ℝ) : ℂ) * Complex.I)) (Ioi 0) :=
      fun s (hs : 0 < s) ↦ by simp only [integral_exp_neg_mul_smul_kernel hs t]
    rw [integral_Ioi_rpow_neg_smul hα1 h0', setIntegral_congr_fun measurableSet_Ioi hL,
      integral_rpow_smul_laplace hα.1 hα.2 t (hint.congr_fun hL measurableSet_Ioi), smul_smul]
  have hneg : ∫ x in Ioi (0 : ℝ), x ^ (-(α + 1)) •
      (Complex.exp ((t * -x : ℝ) * Complex.I) - 1 - (t * sin (-x) : ℝ) * Complex.I) =
      ∫ x in Ioi (0 : ℝ), x ^ (-(α + 1)) •
        (Complex.exp ((-t * x : ℝ) * Complex.I) - 1 - (-t * sin x : ℝ) * Complex.I) := by
    simp only [mul_neg, sin_neg, neg_mul]
  rw [integral_stableLevyMeasure_eq hα hβ (integrable_exp_sub_one_sub_sin_stableLevyMeasure α β t)]
  rw [hneg, hhalf, hhalf, smul_smul, smul_smul, add_comm 1 α]
  have hsin : sin (π * α / 2) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (by nlinarith [pi_pos, hα.1]) (by nlinarith [pi_pos, hα.2])).ne'
  have hΓ : Gamma (α + 1) ≠ 0 := (Gamma_pos_of_pos (by linarith [hα.1])).ne'
  have hcoef (b : ℝ) : Gamma (α + 1) * sin (π * α / 2) / π * b *
      ((Gamma (α + 1))⁻¹ * (π / (2 * sin (π * α / 2)))) = b / 2 := by
    rw [mul_comm π α] at hsin ⊢
    field_simp
  rw [hcoef, hcoef, stableCharacteristicExponent_neg]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.conj_re,
      stableCharacteristicExponent_re hα.1.ne']
    ring
  · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.conj_im,
      stableCharacteristicExponent_im_eq_mul α β t]
    ring

end TauCeti.Probability
