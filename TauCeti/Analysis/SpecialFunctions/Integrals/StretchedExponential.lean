/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Tails with mixed linear and square-root exponential decay

The exponent `v / (√v + ℓ)` changes from linear to square-root growth. The tail
estimate retains that dependence on `ℓ`, which is needed when `ℓ` is the logarithm
of a varying conductor in a prime number estimate.
-/

public section

open MeasureTheory Set

namespace Real

private theorem div_sqrt_add_le_div_sqrt_add {V v ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hV : 0 ≤ V) (hVv : V ≤ v) :
    V / (√V + ℓ) ≤ v / (√v + ℓ) := by
  rcases hV.eq_or_lt with rfl | hV
  · simp [div_nonneg hVv (by positivity : 0 ≤ √v + ℓ)]
  have hv := hV.trans_le hVv
  have hroot : √V ≤ √v := sqrt_le_sqrt hVv
  have hr : √V / (√V + ℓ) ≤ √v / (√v + ℓ) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_right hroot hℓ]
  calc
    V / (√V + ℓ) = √V * (√V / (√V + ℓ)) := by rw [← mul_div_assoc, ← sq, sq_sqrt hV.le]
    _ ≤ √v * (√v / (√v + ℓ)) := by gcongr
    _ = v / (√v + ℓ) := by rw [← mul_div_assoc, ← sq, sq_sqrt hv.le]

private theorem exp_neg_div_sqrt_add_le {c ℓ v : ℝ} (hc : 0 < c) (hℓ : 0 ≤ ℓ) (hv : 0 ≤ v) :
    exp (-(c * (v / (√v + ℓ)))) ≤
      exp (-(c / 2) * √v) + exp (-(c / (2 * (1 + ℓ))) * v) := by
  rcases hv.eq_or_lt with rfl | hv
  · simp
  have hd : 0 < √v + ℓ := by positivity
  by_cases h : ℓ ≤ √v
  · have hroot : √v / 2 ≤ v / (√v + ℓ) := by
      apply (le_div_iff₀ hd).2
      nlinarith [sq_sqrt hv.le, mul_le_mul_of_nonneg_left h (sqrt_nonneg v)]
    exact (exp_le_exp.mpr (by nlinarith)).trans (le_add_of_nonneg_right (exp_nonneg _))
  · have hlin : v / (2 * (1 + ℓ)) ≤ v / (√v + ℓ) :=
      div_le_div_of_nonneg_left hv.le hd (by linarith [lt_of_not_ge h])
    have he : -(c * (v / (√v + ℓ))) ≤ -(c / (2 * (1 + ℓ))) * v := by
      have h := neg_le_neg (mul_le_mul_of_nonneg_left hlin hc.le)
      simpa only [mul_div_assoc, neg_mul, div_mul_eq_mul_div, mul_comm v c] using h
    exact (exp_le_exp.mpr he).trans (le_add_of_nonneg_left (exp_nonneg _))

private theorem integrableOn_exp_mul_sqrt {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun v : ℝ ↦ exp (-r * √v)) (Ioi 0) := by
  simpa [sqrt_eq_rpow] using integrableOn_rpow_mul_exp_neg_mul_rpow (s := 0) (p := 1 / 2)
    (by norm_num) (by norm_num) hr

private theorem integral_exp_mul_sqrt {r : ℝ} (hr : 0 < r) :
    ∫ v in Ioi (0 : ℝ), exp (-r * √v) = 2 / r ^ 2 := by
  have h := integral_exp_neg_mul_rpow (p := 1 / 2) (b := r) (by norm_num) hr
  have hGamma : Gamma (1 / (1 / 2 : ℝ) + 1) = 2 := by
    norm_num [Gamma_nat_eq_factorial 2]
  have hpow : r ^ (-1 / (1 / 2 : ℝ)) = (r ^ 2)⁻¹ := by
    norm_num [rpow_neg hr.le, rpow_two]
  rw [hGamma, hpow] at h
  simpa only [sqrt_eq_rpow, div_eq_mul_inv, mul_comm] using h

/-- The mixed exponential majorant is integrable on the positive ray. -/
theorem integrableOn_exp_neg_div_sqrt_add {c ℓ : ℝ} (hc : 0 < c) (hℓ : 0 ≤ ℓ) :
    IntegrableOn (fun v : ℝ ↦ exp (-(c * (v / (√v + ℓ))))) (Ioi 0) := by
  have hlin : -(c / (2 * (1 + ℓ))) < 0 := neg_neg_of_pos (by positivity)
  have hm : Measurable (fun v : ℝ ↦ exp (-(c * (v / (√v + ℓ))))) := by fun_prop
  refine ((integrableOn_exp_mul_sqrt (half_pos hc)).add (integrableOn_exp_mul_Ioi hlin 0)).mono'
    hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
  rw [norm_of_nonneg (exp_nonneg _)]
  exact exp_neg_div_sqrt_add_le hc hℓ hv.le

/-- Integration preserves the mixed exponential decay up to halving the rate and
multiplying by a factor linear in `ℓ`. -/
theorem integral_Ioi_exp_neg_div_sqrt_add_le {c ℓ V : ℝ} (hc : 0 < c) (hℓ : 0 ≤ ℓ)
    (hV : 0 ≤ V) :
    ∫ v in Ioi V, exp (-(c * (v / (√v + ℓ)))) ≤
      ((1 + ℓ) * (32 / c ^ 2 + 4 / c)) * exp (-(c / 2) * (V / (√V + ℓ))) := by
  let A := exp (-(c / 2) * (V / (√V + ℓ)))
  let r := c / 4
  let s := c / (4 * (1 + ℓ))
  have hr : 0 < r := by positivity
  have hs : 0 < s := by positivity
  let f (v : ℝ) := exp (-r * √v) + exp (-s * v)
  have hf : IntegrableOn f (Ioi 0) :=
    (integrableOn_exp_mul_sqrt hr).add (integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) 0)
  have hsub := Ioi_subset_Ioi hV
  have hb : (∫ v in Ioi V, exp (-(c * (v / (√v + ℓ))))) ≤ ∫ v in Ioi V, A * f v := by
    apply setIntegral_mono_on ((integrableOn_exp_neg_div_sqrt_add hc hℓ).mono_set hsub)
      (IntegrableOn.mono_set (hf.const_mul A) hsub) measurableSet_Ioi
    intro v hv
    have hv₀ := hV.trans hv.le
    have hmono : exp (-(c / 2) * (v / (√v + ℓ))) ≤ A := by
      exact exp_le_exp.mpr (mul_le_mul_of_nonpos_left
        (div_sqrt_add_le_div_sqrt_add hℓ hV hv.le) (by linarith))
    have htail : exp (-(c / 2 * (v / (√v + ℓ)))) ≤ f v := by
      have hrate : c / 2 / (2 * (1 + ℓ)) = s := by dsimp [s]; rw [div_div]; ring_nf
      have hquarter : c / 2 / 2 = r := by dsimp [r]; ring
      simpa only [f, hrate, hquarter] using
        exp_neg_div_sqrt_add_le (half_pos hc) hℓ hv₀
    calc
      exp (-(c * (v / (√v + ℓ)))) =
          exp (-(c / 2) * (v / (√v + ℓ))) * exp (-(c / 2 * (v / (√v + ℓ)))) := by
        rw [← exp_add]
        congr 1
        ring
      _ ≤ A * f v := mul_le_mul hmono htail (exp_nonneg _) (exp_nonneg _)
  refine hb.trans ?_
  rw [integral_const_mul]
  calc
    A * (∫ v in Ioi V, f v) ≤ A * (∫ v in Ioi (0 : ℝ), f v) :=
      mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hf (ae_of_all _ fun v ↦ add_nonneg (exp_nonneg _) (exp_nonneg _))
          (Filter.Eventually.of_forall hsub)) (exp_nonneg _)
    _ = A * (32 / c ^ 2 + 4 * (1 + ℓ) / c) := by
      rw [integral_add (integrableOn_exp_mul_sqrt hr)
        (integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) 0), integral_exp_mul_sqrt hr,
        integral_exp_mul_Ioi (neg_neg_of_pos hs)]
      simp only [mul_zero, exp_zero, div_neg]
      dsimp [r, s]
      congr 1
      field_simp
      ring
    _ ≤ _ := by
      rw [mul_comm _ A]
      gcongr
      nlinarith [mul_nonneg hℓ (by positivity : 0 ≤ 32 / c ^ 2),
        show 4 * (1 + ℓ) / c = (1 + ℓ) * (4 / c) by ring]

end Real

namespace TauCeti

open Real

/-- A bound by the mixed exponential in the logarithmic variable gives absolute
integrability in the original variable against `dt/t`. -/
theorem integrableOn_inv_smul_of_norm_le_exp_neg_div_sqrt_add {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} (hf : StronglyMeasurable f) {c ℓ C : ℝ}
    (hc : 0 < c) (hℓ : 0 ≤ ℓ)
    (hb : ∀ t > 1, ‖f t‖ ≤ C * exp (-(c * (log t / (√(log t) + ℓ))))) :
    IntegrableOn (fun t : ℝ ↦ t⁻¹ • f t) (Ioi 1) := by
  rw [← exp_zero, ← integrableOn_comp_exp_Ioi]
  simp only [smul_smul, mul_inv_cancel₀ (exp_pos _).ne', one_smul]
  refine ((integrableOn_exp_neg_div_sqrt_add hc hℓ).const_mul C).mono'
    (hf.comp_measurable continuous_exp.measurable).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
  simpa only [log_exp] using hb (exp v) (one_lt_exp_iff.mpr hv)

/-- The logarithmic mixed exponential bound transfers to the norm of the `dt/t` tail
in the original variable, retaining the dependence on the decay parameters. -/
theorem norm_integral_Ioi_inv_smul_le_of_norm_le_exp_neg_div_sqrt_add {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {c ℓ C y : ℝ} (hc : 0 < c) (hℓ : 0 ≤ ℓ) (hy : 1 ≤ y)
    (hb : ∀ t > 1, ‖f t‖ ≤ C * exp (-(c * (log t / (√(log t) + ℓ))))) :
    ‖∫ t in Ioi y, t⁻¹ • f t‖ ≤ C * ((1 + ℓ) * (32 / c ^ 2 + 4 / c)) *
      exp (-(c / 2) * (log y / (√(log y) + ℓ))) := by
  have hy₀ := zero_lt_one.trans_le hy
  have hsub := Ioi_subset_Ioi (log_nonneg hy)
  rw [← exp_log hy₀, ← integral_comp_exp_Ioi]
  simp only [smul_smul, mul_inv_cancel₀ (exp_pos _).ne', one_smul, log_exp]
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left
    ((norm_nonneg _).trans (hb 2 one_lt_two)) (exp_pos _)
  by_cases hint : IntegrableOn (fun v ↦ f (exp v)) (Ioi (log y))
  swap
  · rw [integral_undef hint, norm_zero]
    positivity
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    _ ≤ ∫ v in Ioi (log y), C * exp (-(c * (v / (√v + ℓ)))) := by
      refine setIntegral_mono_on hint.norm
        (IntegrableOn.mono_set ((integrableOn_exp_neg_div_sqrt_add hc hℓ).const_mul C) hsub)
        measurableSet_Ioi fun v hv ↦ ?_
      simpa only [log_exp] using hb (exp v) (one_lt_exp_iff.mpr (hsub hv))
    _ ≤ _ := by
      rw [integral_const_mul, mul_assoc C]
      exact mul_le_mul_of_nonneg_left
        (integral_Ioi_exp_neg_div_sqrt_add_le hc hℓ (log_nonneg hy)) hC

end TauCeti
