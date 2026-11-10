/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.CompensatedIntegral
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.MeasureTheory.Integral.RpowLaplace

/-!
# Evaluation of the stable compensated Laplace integral

For a totally skewed stable Lévy measure, the sine-compensated real exponential kernel
is integrable on the allowed half-line. Its integral is a power expression away from shape
one, and a logarithmic expression at shape one. These evaluations give the closed forms of
the stable Laplace exponent, including the sine-compensation location correction.

The Gamma-mixture calculation follows the characteristic-exponent proof in
`TauCeti/Probability/Distributions/Stable/LevyKhintchine.lean`.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
* K. Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge University Press,
  1999, section 14.
-/

public section

noncomputable section

open MeasureTheory Real Set

namespace TauCeti.Probability

private theorem integral_compensatedLevy_eq_mellin {α a : ℝ}
    (hα : α ∈ Ioo 0 2) (ha : 0 ≤ a) :
    ∫ x, exp (-a * x) - 1 + a * sin x ∂stableLevyMeasure α 1 =
      (2 * sin (π * α / 2) / π) *
        ∫ s in Ioi (0 : ℝ), s ^ α * ((s + a)⁻¹ - s⁻¹ + a / (1 + s ^ 2)) := by
  have hg : Integrable (fun x : ℝ ↦ exp (-a * x) - 1 + a * sin x)
      (stableLevyMeasure α 1) := by
    simpa only [neg_mul, sub_neg_eq_add] using
      integrable_exp_mul_sub_one_sub_mul_sin_stableLevyMeasure
        (ae_mul_nonpos_stableLevyMeasure (α := α) (β := 1) (t := -a) (by norm_num)
          (by simpa using ha))
  let c := Gamma (1 + α) * sin (π * α / 2) / π * (1 + 1)
  have hc : c ≠ 0 := by
    have := stableLevyDensity_coefficient_pos hα
    dsimp [c]
    positivity
  have hw : IntegrableOn (fun x : ℝ ↦ x ^ (-(α + 1)) •
      (exp (-a * x) - 1 + a * sin x)) (Ioi 0) := by
    have hd := (integrable_stableLevyDensity_smul_iff α 1).mp hg
    refine IntegrableOn.congr_fun (hd.integrableOn.smul c⁻¹)
      (fun x (hx : 0 < x) ↦ ?_) measurableSet_Ioi
    rw [Pi.smul_apply, stableLevyDensity_of_ne_zero hα (by norm_num) hx.ne',
      ite_eq_left hx, abs_of_pos hx, smul_smul]
    dsimp [c]
    rw [inv_mul_cancel_left₀ hc]
  have hΓ : Gamma (α + 1) ≠ 0 := (Gamma_pos_of_pos (by linarith [hα.1])).ne'
  rw [integral_stableLevyMeasure_eq hα (by norm_num) hg]
  simp only [sub_self, mul_zero, zero_smul, add_zero]
  rw [integral_Ioi_rpow_neg_smul (by linarith [hα.1] : -1 < α) hw]
  simp_rw [smul_eq_mul]
  have hinner : (∫ s in Ioi (0 : ℝ), s ^ α *
      ∫ x in Ioi (0 : ℝ), exp (-(x * s)) * (exp (-a * x) - 1 + a * sin x)) =
      ∫ s in Ioi (0 : ℝ), s ^ α * ((s + a)⁻¹ - s⁻¹ + a / (1 + s ^ 2)) := by
    exact setIntegral_congr_fun measurableSet_Ioi fun s hs ↦ by
      rw [integral_Ioi_exp_neg_mul_mul_exp_sub_one_add_sin hs (add_pos_of_pos_of_nonneg hs ha)]
  rw [hinner, add_comm 1 α, ← mul_assoc]
  congr 1
  field_simp
  ring

/-- Away from shape one, the compensated real exponential integral of a fully skewed stable
Lévy measure is a power term plus its sine-compensation correction. -/
theorem integral_exp_mul_sub_one_sub_mul_sin_stableLevyMeasure_of_ne_one {α β t : ℝ}
    (hα : α ∈ Ioo 0 2) (hα1 : α ≠ 1) (hβ : |β| = 1) (ht : β * t ≤ 0) :
    ∫ x, exp (t * x) - 1 - t * sin x ∂stableLevyMeasure α β =
      -(β * t) * tan (π * α / 2) - |t| ^ α / cos (π * α / 2) := by
  have hplus (u : ℝ) (hu : u ≤ 0) :
      (∫ x, exp (u * x) - 1 - u * sin x ∂stableLevyMeasure α 1) =
        -u * tan (π * α / 2) - |u| ^ α / cos (π * α / 2) := by
    rcases eq_or_lt_of_le hu with rfl | hu
    · simp [zero_rpow hα.1.ne']
    have ha : 0 < -u := by linarith
    have h := integral_compensatedLevy_eq_mellin hα ha.le
    rw [integral_rpow_mul_inv_add_sub_inv_add_div_one_add_sq hα.1 hα.2 hα1 ha] at h
    have hsin : sin (π * α / 2) ≠ 0 :=
      (sin_pos_of_pos_of_lt_pi (by nlinarith [pi_pos, hα.1])
        (by nlinarith [pi_pos, hα.2])).ne'
    have hcos : cos (π * α / 2) ≠ 0 := by
      rcases hα1.lt_or_gt with h1 | h1
      · exact (cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos, hα.1],
          by nlinarith [pi_pos]⟩).ne'
      · exact (cos_neg_of_pi_div_two_lt_of_lt (by nlinarith [pi_pos])
          (by nlinarith [pi_pos, hα.2])).ne
    have hdouble : sin (π * α) = 2 * sin (π * α / 2) * cos (π * α / 2) := by
      calc
        _ = sin (2 * (π * α / 2)) := congrArg sin (by ring)
        _ = _ := sin_two_mul _
    simpa only [neg_neg, neg_mul, sub_eq_add_neg] using h.trans (by
      rw [abs_of_neg hu, tan_eq_sin_div_cos, hdouble]
      field_simp
      ring)
  rcases (abs_eq zero_le_one).mp hβ with rfl | rfl
  · simpa using hplus t (by simpa using ht)
  · have h := hplus (-t) (by linarith)
    rw [← map_neg_stableLevyMeasure α 1, integral_map (by fun_prop) (by fun_prop)]
    simpa [sin_neg, mul_neg, neg_mul] using h

/-- At shape one, the compensated real exponential integral of a fully skewed stable Lévy
measure is logarithmic. The formula includes transform parameter zero. -/
theorem integral_exp_mul_sub_one_sub_mul_sin_stableLevyMeasure_one {β t : ℝ}
    (hβ : |β| = 1) (ht : β * t ≤ 0) :
    ∫ x, exp (t * x) - 1 - t * sin x ∂stableLevyMeasure 1 β =
      -(2 / π) * β * t * log |t| := by
  have hplus (u : ℝ) (hu : u ≤ 0) :
      (∫ x, exp (u * x) - 1 - u * sin x ∂stableLevyMeasure 1 1) =
        -(2 / π) * u * log |u| := by
    rcases eq_or_lt_of_le hu with rfl | hu
    · simp
    have ha : 0 < -u := by linarith
    have h := integral_compensatedLevy_eq_mellin (by norm_num : (1 : ℝ) ∈ Ioo 0 2) ha.le
    simp only [rpow_one] at h
    rw [integral_mul_inv_add_sub_inv_add_div_one_add_sq ha] at h
    simpa [abs_of_neg hu, sub_eq_add_neg, mul_assoc] using h
  rcases (abs_eq zero_le_one).mp hβ with rfl | rfl
  · simpa using hplus t (by simpa using ht)
  · have h := hplus (-t) (by linarith)
    rw [← map_neg_stableLevyMeasure 1 1, integral_map (by fun_prop) (by fun_prop)]
    simpa [sin_neg, mul_neg, neg_mul] using h

end TauCeti.Probability
