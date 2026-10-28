/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Pareto.PDF
public import Mathlib.Probability.ConditionalProbability
public import TauCeti.Analysis.SpecialFunctions.Gamma
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The Lévy measure of a scalar stable law

For `0 < α < 2` and `|β| ≤ 1`, the stable Lévy measure has density proportional to
`|x| ^ (-1 - α)`, with respective weights `1 + β` and `1 - β` on the positive and
negative half-lines. It has no atom at zero. Parameters outside this non-Gaussian range
give the zero measure.

Restricting to either tail gives a multiple of a Pareto law or its reflection. In particular,
removing a positive neighbourhood of zero leaves positive finite mass, and conditioning on
that set gives a probability jump law for compound Poisson approximations.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.

The tail normalization reuses Mathlib's `paretoMeasure` and its probability theorem.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

namespace TauCeti.Probability

variable {α β ε : ℝ}

/-- The real density of the stable Lévy measure, with value zero at zero and outside
`0 < α < 2`, `|β| ≤ 1`. This is a Lévy density, rather than a probability density. -/
def stableLevyDensity (α β x : ℝ) : ℝ :=
  if 0 < α ∧ α < 2 ∧ |β| ≤ 1 ∧ x ≠ 0 then
    Gamma (1 + α) * sin (π * α / 2) / π *
      (if 0 < x then 1 + β else 1 - β) * |x| ^ (-(α + 1))
  else 0

/-- The stable Lévy measure. Its restrictions away from zero supply finite jump measures. -/
def stableLevyMeasure (α β : ℝ) : Measure ℝ :=
  volume.withDensity fun x ↦ ENNReal.ofReal (stableLevyDensity α β x)

/-- The stable Lévy measure is Lebesgue measure weighted by its real density. -/
theorem stableLevyMeasure_def (α β : ℝ) :
    stableLevyMeasure α β =
      volume.withDensity (fun x ↦ ENNReal.ofReal (stableLevyDensity α β x)) := (rfl)

@[simp]
theorem stableLevyDensity_zero (α β : ℝ) : stableLevyDensity α β 0 = 0 := by
  simp [stableLevyDensity]

/-- In the non-Gaussian range, the Lévy density has the prescribed power-law expression off zero. -/
theorem stableLevyDensity_of_ne_zero (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    {x : ℝ} (hx : x ≠ 0) :
    stableLevyDensity α β x = Gamma (1 + α) * sin (π * α / 2) / π *
      (if 0 < x then 1 + β else 1 - β) * |x| ^ (-(α + 1)) := by
  have h : 0 < α ∧ α < 2 ∧ |β| ≤ 1 ∧ x ≠ 0 := ⟨hα.1, hα.2, hβ, hx⟩
  simp [stableLevyDensity, h]

/-- Parameters outside the non-Gaussian range give the zero Lévy density. -/
@[simp]
theorem stableLevyDensity_eq_zero_of_not (h : ¬ (0 < α ∧ α < 2 ∧ |β| ≤ 1)) (x : ℝ) :
    stableLevyDensity α β x = 0 := by
  have hx : ¬ (0 < α ∧ α < 2 ∧ |β| ≤ 1 ∧ x ≠ 0) :=
    fun hx ↦ h ⟨hx.1, hx.2.1, hx.2.2.1⟩
  simp [stableLevyDensity, hx]

/-- Parameters outside the non-Gaussian range give the zero Lévy measure. -/
@[simp]
theorem stableLevyMeasure_eq_zero_of_not (h : ¬ (0 < α ∧ α < 2 ∧ |β| ≤ 1)) :
    stableLevyMeasure α β = 0 := by
  simp [stableLevyMeasure_def, stableLevyDensity_eq_zero_of_not h]

/-- The normalizing coefficient of a non-Gaussian stable Lévy density is positive. -/
theorem stableLevyDensity_coefficient_pos (hα : α ∈ Ioo 0 2) :
    0 < Gamma (1 + α) * sin (π * α / 2) / π := by
  apply div_pos (mul_pos (Gamma_pos_of_pos (by linarith [hα.1])) ?_) pi_pos
  apply sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos pi_pos hα.1) (by norm_num)
  · nlinarith [pi_pos, hα.2]

/-- The real Lévy density is nonnegative for all parameters. -/
theorem stableLevyDensity_nonneg (α β x : ℝ) : 0 ≤ stableLevyDensity α β x := by
  by_cases h : 0 < α ∧ α < 2 ∧ |β| ≤ 1 ∧ x ≠ 0
  · rw [stableLevyDensity_of_ne_zero ⟨h.1, h.2.1⟩ h.2.2.1 h.2.2.2]
    have hb := abs_le.mp h.2.2.1
    exact mul_nonneg
      (mul_nonneg (stableLevyDensity_coefficient_pos ⟨h.1, h.2.1⟩).le
        (by split_ifs <;> linarith)) (rpow_nonneg (abs_nonneg _) _)
  · simp only [stableLevyDensity, ite_eq_right h, le_refl]

/-- The Lévy density is jointly measurable in both shapes and the jump size. -/
@[fun_prop]
theorem measurable_stableLevyDensity :
    Measurable fun p : (ℝ × ℝ) × ℝ ↦ stableLevyDensity p.1.1 p.1.2 p.2 := by
  unfold stableLevyDensity
  have hsign : Measurable fun p : (ℝ × ℝ) × ℝ ↦
      if 0 < p.2 then 1 + p.1.2 else 1 - p.1.2 :=
    Measurable.ite (by measurability) (by fun_prop) (by fun_prop)
  have hcoeff : Measurable fun p : (ℝ × ℝ) × ℝ ↦
      Gamma (1 + p.1.1) * sin (π * p.1.1 / 2) / π := by fun_prop
  exact Measurable.ite (by measurability)
    ((hcoeff.mul hsign).mul (by fun_prop)) measurable_const

/-- The full totalized Lévy measure family is Giry measurable. -/
@[fun_prop]
theorem measurable_stableLevyMeasure :
    Measurable fun p : ℝ × ℝ ↦ stableLevyMeasure p.1 p.2 := by
  simp only [stableLevyMeasure_def]
  exact measurable_withDensity measurable_stableLevyDensity.ennreal_ofReal

/-- The stable Lévy measure has no atoms. -/
instance (α β : ℝ) : NullSingletonClass (stableLevyMeasure α β) := by
  rw [stableLevyMeasure_def]
  infer_instance

/-- The stable Lévy measure is sigma-finite for all parameters. -/
instance (α β : ℝ) : SigmaFinite (stableLevyMeasure α β) := by
  rw [stableLevyMeasure_def]
  infer_instance

/-- Reflection changes the sign of the skewness parameter in the Lévy density. -/
@[simp]
theorem stableLevyDensity_neg (α β x : ℝ) :
    stableLevyDensity α β (-x) = stableLevyDensity α (-β) x := by
  by_cases hx : x = 0
  · simp [hx]
  · have hsign : (if 0 < -x then 1 + β else 1 - β) =
        (if 0 < x then 1 + -β else 1 - -β) := by
      rcases lt_or_gt_of_ne hx with hx | hx <;> simp [hx, not_lt_of_ge hx.le, sub_eq_add_neg]
    simp only [stableLevyDensity, neg_ne_zero, abs_neg, hsign]

/-- Reflecting the stable Lévy measure negates its skewness. -/
theorem map_neg_stableLevyMeasure (α β : ℝ) :
    (stableLevyMeasure α β).map (fun x ↦ -x) = stableLevyMeasure α (-β) := by
  have h := MeasurableEquiv.map_withDensity (MeasurableEquiv.neg ℝ) volume
    (fun x ↦ ENNReal.ofReal (stableLevyDensity α β x))
  simpa only [MeasurableEquiv.neg_apply, Measure.map_neg_eq_self,
    MeasurableEquiv.symm_neg, stableLevyDensity_neg, stableLevyMeasure_def] using h

/-- Above a positive cutoff, the stable Lévy measure is a finite multiple of a Pareto law.
This includes zero positive-tail mass at skewness `-1`. -/
theorem stableLevyMeasure_restrict_Ioi (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hε : 0 < ε) :
    (stableLevyMeasure α β).restrict (Ioi ε) =
      ENNReal.ofReal (Gamma (1 + α) * sin (π * α / 2) / π * (1 + β) /
        (α * ε ^ α)) • paretoMeasure ε α := by
  have hc : 0 ≤ Gamma (1 + α) * sin (π * α / 2) / π * (1 + β) /
      (α * ε ^ α) := by
    exact div_nonneg
      (mul_nonneg (stableLevyDensity_coefficient_pos hα).le (by linarith [(abs_le.mp hβ).1]))
      (mul_nonneg hα.1.le (rpow_nonneg hε.le _))
  rw [stableLevyMeasure_def, paretoMeasure, ← withDensity_smul _ (measurable_paretoPDF ε α),
    restrict_withDensity measurableSet_Ioi, ← withDensity_indicator measurableSet_Ioi]
  apply withDensity_congr_ae
  filter_upwards [(volume : Measure ℝ).ae_ne ε] with x hx
  by_cases hxe : ε < x
  · have hxpos := hε.trans hxe
    simp only [indicator_of_mem (mem_Ioi.mpr hxe), Pi.smul_apply, smul_eq_mul,
      paretoPDF_of_le hxe.le,
      ← ENNReal.ofReal_mul hc, stableLevyDensity_of_ne_zero hα hβ hxpos.ne',
      ite_eq_left hxpos, abs_of_pos hxpos]
    congr 1
    field_simp [hα.1.ne', (rpow_pos_of_pos hε α).ne']
  · have hlt : x < ε := lt_of_le_of_ne (le_of_not_gt hxe) hx
    simp only [indicator_of_notMem (mt mem_Ioi.mp hxe), Pi.smul_apply,
      paretoPDF_of_lt hlt, smul_zero]

/-- The mass above a positive cutoff, including the vanishing tail at skewness `-1`. -/
theorem stableLevyMeasure_Ioi (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) :
    stableLevyMeasure α β (Ioi ε) =
      ENNReal.ofReal (Gamma (1 + α) * sin (π * α / 2) / π * (1 + β) /
        (α * ε ^ α)) := by
  have := isProbabilityMeasure_paretoMeasure hε hα.1
  simpa using congrArg (fun μ : Measure ℝ ↦ μ univ)
    (stableLevyMeasure_restrict_Ioi hα hβ hε)

/-- Below a negative cutoff, the stable Lévy measure is a finite multiple of a reflected Pareto law.
This includes zero negative-tail mass at skewness `1`. -/
theorem stableLevyMeasure_restrict_Iio (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hε : 0 < ε) :
    (stableLevyMeasure α β).restrict (Iio (-ε)) =
      ENNReal.ofReal (Gamma (1 + α) * sin (π * α / 2) / π * (1 - β) /
        (α * ε ^ α)) • (paretoMeasure ε α).map (fun x ↦ -x) := by
  have hpre : (fun x : ℝ ↦ -x) ⁻¹' Iio (-ε) = Ioi ε := by
    ext x
    simp only [mem_preimage, mem_Iio, mem_Ioi, neg_lt_neg_iff]
  have hreflect := map_neg_stableLevyMeasure α (-β)
  simp only [neg_neg] at hreflect
  rw [← hreflect, Measure.restrict_map measurable_neg measurableSet_Iio, hpre,
    stableLevyMeasure_restrict_Ioi hα (by simpa only [abs_neg] using hβ) hε,
    Measure.map_smul _ measurable_neg.aemeasurable, sub_eq_add_neg]

/-- The mass below a negative cutoff, including the vanishing tail at skewness `1`. -/
theorem stableLevyMeasure_Iio (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) :
    stableLevyMeasure α β (Iio (-ε)) =
      ENNReal.ofReal (Gamma (1 + α) * sin (π * α / 2) / π * (1 - β) /
        (α * ε ^ α)) := by
  have := isProbabilityMeasure_paretoMeasure hε hα.1
  simpa [Measure.map_apply measurable_neg] using congrArg (fun μ : Measure ℝ ↦ μ univ)
    (stableLevyMeasure_restrict_Iio hα hβ hε)

/-- Removing a positive neighbourhood of zero leaves finite mass independent of skewness. -/
theorem stableLevyMeasure_abs_gt (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hε : 0 < ε) :
    stableLevyMeasure α β {x | ε < |x|} =
      ENNReal.ofReal (2 * Gamma (1 + α) * sin (π * α / 2) / (π * α * ε ^ α)) := by
  have hset : {x : ℝ | ε < |x|} = Iio (-ε) ∪ Ioi ε := by
    ext x
    simp only [mem_ofPred_eq, mem_union, mem_Iio, mem_Ioi, lt_abs, lt_neg, or_comm]
  have hd : Disjoint (Iio (-ε)) (Ioi ε) := by
    apply disjoint_left.mpr
    intro x hx hy
    simp only [mem_Iio, mem_Ioi] at hx hy
    linarith
  have hc := (stableLevyDensity_coefficient_pos hα).le
  have hden : 0 ≤ α * ε ^ α := mul_nonneg hα.1.le (rpow_nonneg hε.le _)
  rw [hset, measure_union hd measurableSet_Ioi,
    stableLevyMeasure_Iio hα hβ hε, stableLevyMeasure_Ioi hα hβ hε,
    ← ENNReal.ofReal_add (div_nonneg (mul_nonneg hc (by linarith [(abs_le.mp hβ).2])) hden)
      (div_nonneg (mul_nonneg hc (by linarith [(abs_le.mp hβ).1])) hden)]
  congr 1
  ring

/-- The cutoff Lévy measure has positive mass, even at either full-skewness boundary. -/
theorem stableLevyMeasure_abs_gt_pos (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hε : 0 < ε) :
    0 < stableLevyMeasure α β {x | ε < |x|} := by
  rw [stableLevyMeasure_abs_gt hα hβ hε]
  apply ENNReal.ofReal_pos.mpr
  have hcoeff := stableLevyDensity_coefficient_pos hα
  have hden : 0 < α * ε ^ α := mul_pos hα.1 (rpow_pos_of_pos hε _)
  have heq : 2 * Gamma (1 + α) * sin (π * α / 2) / (π * α * ε ^ α) =
      2 * (Gamma (1 + α) * sin (π * α / 2) / π) / (α * ε ^ α) := by ring
  rw [heq]
  positivity

/-- The cutoff Lévy measure has finite mass. -/
theorem stableLevyMeasure_abs_gt_ne_top (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hε : 0 < ε) :
    stableLevyMeasure α β {x | ε < |x|} ≠ ∞ := by
  rw [stableLevyMeasure_abs_gt hα hβ hε]
  exact ENNReal.ofReal_ne_top

/-- Restricting the stable Lévy measure away from zero gives a finite measure. -/
theorem isFiniteMeasure_stableLevyMeasure_restrict_abs_gt (hα : α ∈ Ioo 0 2)
    (hβ : |β| ≤ 1) (hε : 0 < ε) :
    IsFiniteMeasure ((stableLevyMeasure α β).restrict {x | ε < |x|}) :=
  isFiniteMeasure_restrict.mpr (stableLevyMeasure_abs_gt_ne_top hα hβ hε)

/-- Normalizing jumps larger than a positive cutoff gives a probability jump law. -/
theorem isProbabilityMeasure_cond_stableLevyMeasure (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (hε : 0 < ε) :
    IsProbabilityMeasure (cond (stableLevyMeasure α β) {x | ε < |x|}) := by
  exact cond_isProbabilityMeasure_of_finite (stableLevyMeasure_abs_gt_pos hα hβ hε).ne'
    (stableLevyMeasure_abs_gt_ne_top hα hβ hε)

end TauCeti.Probability
