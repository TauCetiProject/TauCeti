/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Stable.Approximation.Tails
public import TauCeti.Probability.Distributions.Stable.Operations
import TauCeti.Probability.Distributions.Stable.SmallJump.Limit
import TauCeti.Probability.Moments.Tail
import TauCeti.MeasureTheory.Function.L1Space.Integrable

/-!
# Power-law tails of scalar stable laws

For a non-Gaussian stable shape `0 < α < 2`, the right and left tail constants are
`stableTailConstant α * s ^ α * (1 + β)` and
`stableTailConstant α * s ^ α * (1 - β)`, respectively. These limits hold at shape one,
at both fully skewed boundaries, and at zero scale. A zero constant is a limit statement,
not an asymptotic equivalence to zero.

The large-jump component supplies the constants. Its independent small-jump factor has a
finite second moment, so its absolute moment of order `α < 2` is finite and it does not
change either constant. Positive scaling and translation then give all scales and locations.
The final two theorems transport the limits to random variables with the specified law.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {α β : ℝ} {s : ℝ≥0} {m : ℝ}

/-- The small-jump factor preserves the standardized right-tail constant. -/
private theorem tendsto_rpow_mul_standardStableMeasure_real_Ioi
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) :
    Tendsto (fun x : ℝ ↦ x ^ α * (stableMeasure α β 1 0).real (Ioi x)) atTop
      (𝓝 (stableTailConstant α * (1 + β))) := by
  obtain ⟨μ, hμ, -⟩ := existsUnique_conv_stableCompensatedPoissonMeasure_eq hα hβ zero_lt_one
  let _ := isProbabilityMeasure_stableCompensatedPoissonMeasure α β 1
  have hαtwo : ENNReal.ofReal α ≤ 2 := by
    exact_mod_cast hα.2.le
  have hsmall := (memLp_two_id_of_conv_stableCompensatedPoissonMeasure_eq
    hα hβ zero_lt_one hμ).mono_exponent hαtwo
  have hint := (TauCeti.memLp_id_ofReal_iff_integrable_abs_rpow hα.1 _).1 hsmall
  have htail := (stableCompensatedPoissonMeasure α β 1).tendsto_rpow_mul_conv_real_Ioi
    (μ : Measure ℝ) hα.1
    (tendsto_rpow_mul_stableCompensatedPoissonMeasure_real_Ioi hα hβ zero_lt_one) hint
  simpa only [Measure.conv_comm, hμ, measureReal_def, measure_univ, ENNReal.toReal_one,
    mul_one] using htail

/-- The right tail of a non-Gaussian stable law has the stable power-law constant.
This includes zero scale and the zero constant at full negative skewness. -/
theorem tendsto_rpow_mul_stableMeasure_real_Ioi
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) :
    Tendsto (fun x : ℝ ↦ x ^ α * (stableMeasure α β s m).real (Ioi x)) atTop
      (𝓝 (stableTailConstant α * (s : ℝ) ^ α * (1 + β))) := by
  by_cases hs : s = 0
  · subst s
    rw [stableMeasure_zero_scale ⟨hα.1, hα.2.le⟩ hβ]
    simp only [NNReal.coe_zero, zero_rpow hα.1.ne', mul_zero, zero_mul]
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop m] with x hx
    simp [measureReal_def, hx.not_gt]
  have hspos : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have hstd := tendsto_rpow_mul_standardStableMeasure_real_Ioi hα hβ
  have hlim := (hstd.rpow_mul_comp_const_mul (inv_pos.mpr hspos)).rpow_mul_comp_add (-m)
  have hconstant : stableTailConstant α * (1 + β) / ((s : ℝ)⁻¹) ^ α =
      stableTailConstant α * (s : ℝ) ^ α * (1 + β) := by
    rw [inv_rpow s.coe_nonneg, div_inv_eq_mul]
    ring
  rw [hconstant] at hlim
  apply hlim.congr
  intro x
  rw [← stableMeasure_one_zero_map_affine (s := s) (m := m),
    map_measureReal_apply (by fun_prop) measurableSet_Ioi]
  congr 2
  ext y
  simp only [mem_preimage, mem_Ioi]
  rw [mul_comm ((s : ℝ)⁻¹), ← div_eq_mul_inv, div_lt_iff₀ hspos]
  constructor <;> intro h <;> linarith

/-- The left tail of a non-Gaussian stable law has the stable power-law constant.
This includes zero scale and the zero constant at full positive skewness. -/
theorem tendsto_rpow_mul_stableMeasure_real_Iio_neg
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) :
    Tendsto (fun x : ℝ ↦ x ^ α * (stableMeasure α β s m).real (Iio (-x))) atTop
      (𝓝 (stableTailConstant α * (s : ℝ) ^ α * (1 - β))) := by
  have h := tendsto_rpow_mul_stableMeasure_real_Ioi (β := -β) (s := s) (m := -m) hα
    (by simpa only [abs_neg] using hβ)
  rw [← stableMeasure_map_neg α β s m] at h
  simpa only [Measure.map_neg_real_Ioi, sub_eq_add_neg, neg_neg] using h

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
  {α β : ℝ} {s : ℝ≥0} {m : ℝ}

/-- A stable random variable has the right-tail constant of its law, including the
fully skewed and zero-scale boundaries. -/
theorem tendsto_rpow_mul_measureReal_gt_stableMeasure
    (hX : HasLaw X (TauCeti.Probability.stableMeasure α β s m) P)
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) :
    Tendsto (fun x : ℝ ↦ x ^ α * P.real {ω | x < X ω}) atTop
      (𝓝 (TauCeti.Probability.stableTailConstant α * (s : ℝ) ^ α * (1 + β))) := by
  have h := TauCeti.Probability.tendsto_rpow_mul_stableMeasure_real_Ioi (s := s) (m := m) hα hβ
  apply h.congr
  intro x
  congr 1
  simpa only [Ioi_def] using
    (hX.measureReal_eq (p := fun y ↦ x < y) (by measurability)).symm

/-- A stable random variable has the left-tail constant of its law, including the
fully skewed and zero-scale boundaries. -/
theorem tendsto_rpow_mul_measureReal_lt_neg_stableMeasure
    (hX : HasLaw X (TauCeti.Probability.stableMeasure α β s m) P)
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) :
    Tendsto (fun x : ℝ ↦ x ^ α * P.real {ω | X ω < -x}) atTop
      (𝓝 (TauCeti.Probability.stableTailConstant α * (s : ℝ) ^ α * (1 - β))) := by
  have h := TauCeti.Probability.tendsto_rpow_mul_stableMeasure_real_Iio_neg
    (s := s) (m := m) hα hβ
  apply h.congr
  intro x
  congr 1
  simpa only [Iio_def] using
    (hX.measureReal_eq (p := fun y ↦ y < -x) (by measurability)).symm

end ProbabilityTheory.HasLaw
