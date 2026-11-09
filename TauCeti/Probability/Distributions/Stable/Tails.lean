/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Stable.LevyMeasure

/-!
# Tail constants of stable Lévy measures

The Lévy intensity used to construct a non-Gaussian scalar stable law has exact power-law
tails. This file records the corresponding real-valued identities and their asymptotic form.
They isolate the constants that enter the one-big-jump analysis of stable-law tails.

For shape `α` and skewness `β`, multiplication of the right and left tail masses by `x ^ α`
gives respectively

`Gamma α * sin (π * α / 2) / π * (1 + β)`

and

`Gamma α * sin (π * α / 2) / π * (1 - β)`.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, Chapter 1.
-/

public section

noncomputable section

open Filter MeasureTheory Real Set
open scoped ENNReal Topology

namespace TauCeti.Probability

variable {α β : ℝ}

/-- The universal power-law tail constant for a scalar stable law of shape `α`. -/
def stableTailConstant (α : ℝ) : ℝ :=
  Gamma α * sin (π * α / 2) / π

/-- The stable tail constant in terms of the Gamma and sine functions. -/
theorem stableTailConstant_def (α : ℝ) :
    stableTailConstant α = Gamma α * sin (π * α / 2) / π := (rfl)

/-- The stable tail constant is positive throughout the non-Gaussian shape range. -/
theorem stableTailConstant_pos (hα : α ∈ Ioo 0 2) : 0 < stableTailConstant α := by
  rw [stableTailConstant]
  apply div_pos (mul_pos (Gamma_pos_of_pos hα.1) ?_) pi_pos
  apply sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos pi_pos hα.1) (by norm_num)
  · nlinarith [pi_pos, hα.2]

/-- The normalized right-tail mass of a stable Lévy measure is constant. -/
theorem rpow_mul_toReal_stableLevyMeasure_Ioi (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    {x : ℝ} (hx : 0 < x) :
    x ^ α * (stableLevyMeasure α β (Ioi x)).toReal =
      stableTailConstant α * (1 + β) := by
  rw [stableTailConstant]
  rw [stableLevyMeasure_Ioi hα hβ hx]
  rw [ENNReal.toReal_ofReal]
  · rw [add_comm 1 α, Gamma_add_one hα.1.ne']
    field_simp [hα.1.ne', (rpow_pos_of_pos hx α).ne']
  · exact div_nonneg
      (mul_nonneg (stableLevyDensity_coefficient_pos hα).le
        (by linarith [(abs_le.mp hβ).1]))
      (mul_nonneg hα.1.le (rpow_nonneg hx.le α))

/-- The normalized left-tail mass of a stable Lévy measure is constant. -/
theorem rpow_mul_toReal_stableLevyMeasure_Iio (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    {x : ℝ} (hx : 0 < x) :
    x ^ α * (stableLevyMeasure α β (Iio (-x))).toReal =
      stableTailConstant α * (1 - β) := by
  rw [stableTailConstant]
  rw [stableLevyMeasure_Iio hα hβ hx]
  rw [ENNReal.toReal_ofReal]
  · rw [add_comm 1 α, Gamma_add_one hα.1.ne']
    field_simp [hα.1.ne', (rpow_pos_of_pos hx α).ne']
  · exact div_nonneg
      (mul_nonneg (stableLevyDensity_coefficient_pos hα).le
        (by linarith [(abs_le.mp hβ).2]))
      (mul_nonneg hα.1.le (rpow_nonneg hx.le α))

/-- The right tail of a stable Lévy measure has its stable power-law constant at infinity. -/
theorem tendsto_rpow_mul_toReal_stableLevyMeasure_Ioi (hα : α ∈ Ioo 0 2)
    (hβ : |β| ≤ 1) :
    Tendsto (fun x : ℝ ↦ x ^ α * (stableLevyMeasure α β (Ioi x)).toReal) atTop
      (nhds (stableTailConstant α * (1 + β))) := by
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_gt_atTop 0] with x hx
  exact rpow_mul_toReal_stableLevyMeasure_Ioi hα hβ hx

/-- The left tail of a stable Lévy measure has its stable power-law constant at infinity. -/
theorem tendsto_rpow_mul_toReal_stableLevyMeasure_Iio (hα : α ∈ Ioo 0 2)
    (hβ : |β| ≤ 1) :
    Tendsto (fun x : ℝ ↦ x ^ α * (stableLevyMeasure α β (Iio (-x))).toReal) atTop
      (nhds (stableTailConstant α * (1 - β))) := by
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_gt_atTop 0] with x hx
  exact rpow_mul_toReal_stableLevyMeasure_Iio hα hβ hx

end TauCeti.Probability
