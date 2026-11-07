/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Growth
public import TauCeti.Analysis.Complex.GrowthOrder.Logarithmic
public import Mathlib.Analysis.MellinTransform
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Growth bounds for Mellin tails with exponential decay

The tail over `(1, ∞)` of `u^R exp(-c u^α) du/u` is bounded by the positive Gamma
moment at `(R+1)/α`, for `R ≥ 0` and `c, α > 0`. In particular this bound remains
finite at `R = 0`. These estimates provide the quantitative ingredient for the
split Mellin method of proving order-one growth for completed L-functions.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 5.
-/

public section

open Real Set MeasureTheory Filter Topology Asymptotics

namespace TauCeti
/-- The exponentially decaying Mellin-tail majorant is integrable for every nonnegative power. -/
theorem integrableOn_rpow_mul_exp_neg_mul_rpow_div {R c α : ℝ}
    (hR : 0 ≤ R) (hc : 0 < c) (hα : 0 < α) :
    IntegrableOn (fun u : ℝ ↦ u ^ R * exp (-c * u ^ α) / u) (Ioi 1) := by
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < R) hα hc
  apply (hg.mono_set (Ioi_subset_Ioi zero_le_one)).mono' ?_ ?_
  · exact (by fun_prop : Measurable (fun u : ℝ ↦ u ^ R * exp (-c * u ^ α) / u)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans zero_lt_one hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_self (by positivity) (le_of_lt hu)

/-- A Mellin-tail moment is bounded by the shifted Gamma moment, including exponent zero. -/
theorem integral_rpow_mul_exp_neg_mul_rpow_div_le_Gamma {R c α : ℝ}
    (hR : 0 ≤ R) (hc : 0 < c) (hα : 0 < α) :
    (∫ u in Ioi 1, u ^ R * exp (-c * u ^ α) / u) ≤
      c ^ (-(R + 1) / α) * Gamma ((R + 1) / α) / α := by
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < R) hα hc
  calc
    (∫ u in Ioi 1, u ^ R * exp (-c * u ^ α) / u) ≤
        ∫ u in Ioi 1, u ^ R * exp (-c * u ^ α) := by
      apply setIntegral_mono_on (integrableOn_rpow_mul_exp_neg_mul_rpow_div hR hc hα)
        (hg.mono_set (Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi
      intro u hu
      have hu0 : 0 < u := lt_trans zero_lt_one hu
      exact div_le_self (by positivity) (le_of_lt hu)
    _ ≤ ∫ u in Ioi 0, u ^ R * exp (-c * u ^ α) := by
      apply setIntegral_mono_set hg
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu0 : 0 < u := hu
        positivity
      · exact Eventually.of_forall (fun u hu ↦ lt_trans zero_lt_one hu)
    _ = _ := by
      rw [integral_rpow_mul_exp_neg_mul_rpow hα (by linarith : -1 < R) hc]
      ring


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem norm_mellinIntegrand_le {f : ℝ → E} {C₀ c α : ℝ}
    {s : ℂ} {u : ℝ} (hu : 1 < u)
    (hbound : ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) :
    ‖(u : ℂ) ^ (s - 1) • f u‖ ≤ C₀ * (u ^ ‖s‖ * exp (-c * u ^ α) / u) := by
  have hu0 : 0 < u := zero_lt_one.trans hu
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.sub_re, Complex.one_re,
    rpow_sub hu0, rpow_one]
  calc
    u ^ (s.re) / u * ‖f u‖ ≤ (u ^ ‖s‖ / u) * (C₀ * exp (-c * u ^ α)) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right
          (rpow_le_rpow_of_exponent_le hu.le (Complex.re_le_norm s)) hu0.le
      · exact hbound
      · exact norm_nonneg _
      · positivity
    _ = _ := by ring

/-- Exponential tail decay makes the upper Mellin integral absolutely convergent at every
complex argument. -/
theorem integrableOn_cpow_smul_of_norm_le_exp_neg_mul_rpow {f : ℝ → E}
    {C₀ c α : ℝ} (hc : 0 < c) (hα : 0 < α)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 1)))
    (hbound : ∀ u ∈ Ioi 1, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) (s : ℂ) :
    IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) • f u) (Ioi 1) := by
  have hi := (integrableOn_rpow_mul_exp_neg_mul_rpow_div (norm_nonneg s) hc hα).const_mul C₀
  apply hi.mono' ?_ ?_
  · have hcpow : ContinuousOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1)) (Ioi 1) := by
      apply ContinuousOn.cpow_const (by fun_prop)
      intro u hu
      exact Or.inl (by simpa using (zero_lt_one.trans hu))
    exact hcpow.aestronglyMeasurable measurableSet_Ioi |>.smul hf
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact norm_mellinIntegrand_le hu (hbound u hu)

/-- The norm of the upper Mellin integral is bounded by its positive Gamma moment. -/
theorem norm_integral_cpow_smul_le_mul_Gamma {f : ℝ → E} {C₀ c α : ℝ}
    (hC₀ : 0 ≤ C₀) (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi 1, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) (s : ℂ) :
    ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u‖ ≤
      C₀ * (c ^ (-(‖s‖ + 1) / α) * Gamma ((‖s‖ + 1) / α) / α) := by
  calc
    _ ≤ ∫ u in Ioi 1, C₀ * (u ^ ‖s‖ * exp (-c * u ^ α) / u) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_rpow_mul_exp_neg_mul_rpow_div (norm_nonneg s) hc hα).const_mul C₀)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact norm_mellinIntegrand_le hu (hbound u hu)
    _ = C₀ * ∫ u in Ioi 1, u ^ ‖s‖ * exp (-c * u ^ α) / u := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_rpow_mul_exp_neg_mul_rpow_div_le_Gamma (norm_nonneg s) hc hα) hC₀

/-- An exponentially decaying kernel gives logarithmic-exponential growth of its upper Mellin
integral, uniformly over the whole complex plane. -/
theorem exists_norm_integral_cpow_smul_le_exp_mul_log {f : ℝ → E} {C₀ c α : ℝ}
    (hC₀ : 0 ≤ C₀) (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi 1, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) :
    ∃ C > 0, ∀ s : ℂ, ‖∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) • f u‖ ≤
      exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) := by
  obtain ⟨C, hC, hCG⟩ := exists_rpow_mul_Gamma_div_le_exp_mul_log hc hα
  refine ⟨C + 2 * C₀, by positivity, fun s ↦ ?_⟩
  have hL : (1 / 2 : ℝ) ≤ log (2 + ‖s‖) := by
    have h2 : (1 / 2 : ℝ) ≤ log 2 := by
      convert one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2) using 1; norm_num
    exact h2.trans (log_le_log (by norm_num) (by linarith [norm_nonneg s]))
  calc
    _ ≤ C₀ * (c ^ (-(‖s‖ + 1) / α) * Gamma ((‖s‖ + 1) / α) / α) :=
      norm_integral_cpow_smul_le_mul_Gamma hC₀ hc hα hbound s
    _ ≤ exp C₀ * exp (C * (1 + ‖s‖) * log (2 + ‖s‖)) :=
      mul_le_mul (by linarith [add_one_le_exp C₀]) (hCG ‖s‖ (norm_nonneg s))
        (by positivity) (by positivity)
    _ = exp (C₀ + C * (1 + ‖s‖) * log (2 + ‖s‖)) := (exp_add _ _).symm
    _ ≤ _ := by
      apply exp_le_exp.mpr
      have hRL : (1 / 2 : ℝ) ≤ (1 + ‖s‖) * log (2 + ‖s‖) := by
        nlinarith [norm_nonneg s]
      nlinarith [mul_le_mul_of_nonneg_left hRL hC₀]

/-- The upper Mellin transform of an exponentially decaying complex kernel has order at most
one. -/
theorem orderLE_integral_cpow_mul_of_norm_le_exp_neg_mul_rpow {f : ℝ → ℂ}
    {C₀ c α : ℝ} (hC₀ : 0 ≤ C₀) (hc : 0 < c) (hα : 0 < α)
    (hbound : ∀ u ∈ Ioi 1, ‖f u‖ ≤ C₀ * exp (-c * u ^ α)) :
    OrderLE (fun s ↦ ∫ (u : ℝ) in Ioi 1, (u : ℂ) ^ (s - 1) * f u) 1 := by
  obtain ⟨C, _, hC⟩ := exists_norm_integral_cpow_smul_le_exp_mul_log hC₀ hc hα hbound
  exact orderLE_one_of_norm_le_exp_mul_log hC

end TauCeti
