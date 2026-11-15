/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Basic
public import Mathlib.Probability.HasLaw
import TauCeti.Probability.Distributions.Stable.LargeJumps
import TauCeti.Probability.Distributions.Stable.SmallJump.Limit
import TauCeti.Probability.Distributions.Stable.Operations
import TauCeti.Probability.Distributions.Affine
import TauCeti.MeasureTheory.Function.L1Space.Integrable
import TauCeti.Probability.Moments.Fractional
import TauCeti.Analysis.SpecialFunctions.Integrals.ExpPower
import TauCeti.Analysis.SpecialFunctions.Gamma.FractionalMoment
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-!
# Absolute moments of scalar stable laws

A positive-scale non-Gaussian stable law has a finite absolute moment of positive real
order `q` exactly when `q < α`. The critical exponent diverges, including at shape one and
both fully skewed boundaries. Gaussian and zero-scale laws have every positive-order moment.
The criterion is also stated for arbitrary random variables with a stable law.

The large-jump component has the sharp moment threshold. Its independent small-jump
factor has a finite second moment, which supplies every order below the non-Gaussian shape.
Conversely, Fubini applied to a finite absolute moment of the convolution gives a translated
large-jump component with that moment. Translation preserves moment finiteness, so the
large-jump obstruction persists in the full stable law.

A symmetric stable law with location `m`, scale `s` and shape `α` has, for `0 < q < α`,

`E[|X - m| ^ q] = s ^ q * 2 ^ q * Γ((q + 1) / 2) * Γ(1 - q / α) / (√π * Γ(1 - q / 2))`.

Centering reduces this to location zero, where the characteristic function is the real
function `exp (-|s t| ^ α)`. Its fractional absolute moments are recovered from the
power-weighted integral of `1 - exp (-|s t| ^ α)`, which is a Gamma value. Euler's reflection
and Legendre's duplication formulas then bring the cosine-kernel coefficient into the
conventional form above. The formula covers shape two, where the law is Gaussian with variance
`2 * s ^ 2`.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
* G. Samorodnitsky, M. S. Taqqu, *Stable Non-Gaussian Random Processes*, Chapman & Hall, 1994,
  section 1.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {α β q : ℝ} {s : ℝ≥0} {m : ℝ}

/-- The standardized law inherits the exact large-jump moment threshold. -/
private theorem integrable_abs_rpow_standardStableMeasure_iff
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hq : 0 < q) :
    Integrable (fun x : ℝ ↦ |x| ^ q) (stableMeasure α β 1 0) ↔ q < α := by
  obtain ⟨μ, hμ, -⟩ := existsUnique_conv_stableCompensatedPoissonMeasure_eq hα hβ
    (by norm_num : (0 : ℝ) < 1)
  let _ := isProbabilityMeasure_stableCompensatedPoissonMeasure α β 1
  constructor
  · intro h
    rw [← hμ] at h
    obtain ⟨x, hx⟩ := ((integrable_conv_iff (by fun_prop)).1 h).1.exists
    have hmap : Integrable (fun y : ℝ ↦ |y| ^ q)
        ((stableCompensatedPoissonMeasure α β 1).map (fun y ↦ x + 1 * y)) := by
      exact (integrable_map_measure (by fun_prop) (by fun_prop)).2
        (by simpa only [Function.comp_def, one_mul] using hx)
    have hlarge := (memLp_id_map_affine_iff (a := x) (b := 1) one_ne_zero).1
      ((memLp_id_ofReal_iff_integrable_abs_rpow hq _).2 hmap)
    exact (integrable_abs_rpow_stableCompensatedPoissonMeasure_iff hα hβ zero_lt_one hq).1
      ((memLp_id_ofReal_iff_integrable_abs_rpow hq _).1 hlarge)
  · intro hqα
    have hq_two : ENNReal.ofReal q ≤ 2 := by
      calc ENNReal.ofReal q ≤ ENNReal.ofReal 2 :=
            ENNReal.ofReal_le_ofReal (hqα.trans hα.2).le
           _ = 2 := by norm_num
    have hsmall := (memLp_two_id_of_conv_stableCompensatedPoissonMeasure_eq
      hα zero_lt_one hμ).mono_exponent hq_two
    have hlarge := (memLp_id_ofReal_iff_integrable_abs_rpow hq _).2
      ((integrable_abs_rpow_stableCompensatedPoissonMeasure_iff hα hβ zero_lt_one hq).2 hqα)
    apply (memLp_id_ofReal_iff_integrable_abs_rpow hq _).1
    rw [← hμ, Measure.conv, memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)]
    exact (hsmall.comp_fst _).add (hlarge.comp_snd _)

/-- A valid scalar stable law has a finite positive real-order absolute moment exactly
below its shape, except that zero-scale and Gaussian laws have every such moment.
In particular, the positive-scale non-Gaussian critical exponent is not integrable. -/
@[simp]
theorem integrable_abs_rpow_stableMeasure_iff (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (hq : 0 < q) :
    Integrable (fun x : ℝ ↦ |x| ^ q) (stableMeasure α β s m) ↔
      s = 0 ∨ α = 2 ∨ q < α := by
  by_cases hs : s = 0
  · subst s
    simp only [stableMeasure_zero_scale hα hβ, true_or, iff_true]
    exact integrable_dirac (by finiteness)
  by_cases htwo : α = 2
  · subst α
    simp only [stableMeasure_two hβ, true_or, or_true, iff_true]
    exact (memLp_id_ofReal_iff_integrable_abs_rpow hq _).1
      (memLp_id_gaussianReal' _ ENNReal.ofReal_ne_top)
  have hspos : 0 < (s : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hs)
  have hmap : (stableMeasure α β 1 0).map (fun x ↦ m + (s : ℝ) * x) =
      stableMeasure α β s m := by
    simpa [Real.sign_of_pos hspos] using
      (stableMeasure_map_affine (α := α) (β := β) (s := 1) (m := 0)
        (a := m) (b := (s : ℝ)) (Or.inl hspos.ne'))
  simp only [hs, htwo, false_or]
  rw [← hmap, ← memLp_id_ofReal_iff_integrable_abs_rpow hq,
    memLp_id_map_affine_iff hspos.ne', memLp_id_ofReal_iff_integrable_abs_rpow hq]
  exact integrable_abs_rpow_standardStableMeasure_iff ⟨hα.1, lt_of_le_of_ne hα.2 htwo⟩ hβ hq

/-- The fractional absolute central moments of a symmetric stable law: for `0 < q < α`,
`E[|X - m| ^ q] = s ^ q * 2 ^ q * Γ((q + 1) / 2) * Γ(1 - q / α) / (√π * Γ(1 - q / 2))`.
This includes the Gaussian shape `α = 2` and the zero-scale Dirac law. -/
theorem integral_abs_sub_rpow_stableMeasure (hα : α ∈ Ioc 0 2) (hq : 0 < q) (hqα : q < α)
    (s : ℝ≥0) (m : ℝ) :
    ∫ x, |x - m| ^ q ∂stableMeasure α 0 s m =
      s ^ q * 2 ^ q * Gamma ((q + 1) / 2) * Gamma (1 - q / α) / (√π * Gamma (1 - q / 2)) := by
  have hβ : |(0 : ℝ)| ≤ 1 := by simp
  rcases eq_or_ne s 0 with rfl | hs
  · simp [stableMeasure_zero_scale hα hβ, zero_rpow hq.ne']
  have hspos : 0 < (s : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hs)
  have hcenter : (stableMeasure α 0 s m).map (fun x ↦ x - m) = stableMeasure α 0 s 0 := by
    simpa [← sub_eq_neg_add] using stableMeasure_map_affine (α := α) (β := 0) (s := s)
      (m := m) (a := -m) (b := 1) (Or.inl one_ne_zero)
  rw [← integral_map_of_stronglyMeasurable (μ := stableMeasure α 0 s m)
    (f := fun x : ℝ ↦ |x| ^ q) (by fun_prop) (by fun_prop), hcenter]
  set ν := stableMeasure α 0 s 0 with hν
  have := isProbabilityMeasure_stableMeasure hα hβ s 0
  -- The power-weighted characteristic-function deficit is a rescaled Gamma integral.
  have hdeficit : ∫ t in Ioi (0 : ℝ), t ^ (-(q + 1)) * (ν.real univ - (charFun ν t).re) =
      s ^ q * (Gamma (1 - q / α) / q) := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), t ^ (-(q + 1)) * (1 - exp (-(s * t) ^ α)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
        rw [hν, probReal_univ,
          charFun_stableMeasure_zero_skew_zero_location_re hα,
          abs_of_pos (mul_pos hspos ht)]
      _ = _ := integral_Ioi_rpow_neg_mul_one_sub_exp_neg_mul_rpow hspos hq hqα
  have hbridge := integral_rpow_mul_sub_re_charFun (μ := ν) hq (hqα.trans_le hα.2)
    ((integrable_abs_rpow_stableMeasure_iff hα hβ hq).2 (Or.inr (Or.inr hqα)))
  rw [hdeficit] at hbridge
  have hΓ : Gamma (q + 1) ≠ 0 := (Gamma_pos_of_pos (by linarith)).ne'
  have hsin : sin (π * q / 2) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos, hα.2])).ne'
  have hsin' : sin (q * π / 2) ≠ 0 := by simpa only [mul_comm] using hsin
  have hmoment : ∫ x, |x| ^ q ∂ν =
      s ^ q * Gamma (1 - q / α) * (2 * Gamma (q + 1) * sin (π * q / 2) / (π * q)) := by
    field_simp at hbridge ⊢
    linear_combination -hbridge
  rw [hmoment, two_mul_Gamma_add_one_mul_sin_pi_div_two_div hq]
  ring

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

/-- A random variable with a valid stable law has the same sharp positive-order absolute
moment criterion as that law, with Gaussian and zero-scale exceptions. -/
theorem integrable_abs_rpow_iff_stableMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {α β q : ℝ} {s : ℝ≥0} {m : ℝ}
    (hX : HasLaw X (TauCeti.Probability.stableMeasure α β s m) P)
    (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1) (hq : 0 < q) :
    Integrable (fun ω ↦ |X ω| ^ q) P ↔ s = 0 ∨ α = 2 ∨ q < α := by
  have h := integrable_map_measure (g := fun x : ℝ ↦ |x| ^ q) (by fun_prop) hX.aemeasurable
  rw [hX.map_eq] at h
  exact h.symm.trans (TauCeti.Probability.integrable_abs_rpow_stableMeasure_iff hα hβ hq)

/-- A random variable with a symmetric stable law has the fractional absolute central moments
`s ^ q * 2 ^ q * Γ((q + 1) / 2) * Γ(1 - q / α) / (√π * Γ(1 - q / 2))` for `0 < q < α`. -/
theorem integral_abs_sub_rpow_stableMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {α q : ℝ} {s : ℝ≥0} {m : ℝ}
    (hX : HasLaw X (TauCeti.Probability.stableMeasure α 0 s m) P)
    (hα : α ∈ Ioc 0 2) (hq : 0 < q) (hqα : q < α) :
    ∫ ω, |X ω - m| ^ q ∂P =
      s ^ q * 2 ^ q * Gamma ((q + 1) / 2) * Gamma (1 - q / α) / (√π * Gamma (1 - q / 2)) :=
  (hX.integral_comp (f := fun x ↦ |x - m| ^ q) (by fun_prop)).trans
    (TauCeti.Probability.integral_abs_sub_rpow_stableMeasure hα hq hqα s m)

end ProbabilityTheory.HasLaw
