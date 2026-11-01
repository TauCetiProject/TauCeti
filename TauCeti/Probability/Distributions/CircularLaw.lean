/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Probability.ConditionalProbability

/-!
# The circular law

The circular law is the uniform probability measure on the open unit disc of `ℂ`, with density
`π⁻¹ 1_{|z| < 1}` with respect to the area measure.

## Main definitions

* `TauCeti.Probability.circularLaw`: the uniform probability measure on the unit disc,
  `ProbabilityTheory.cond volume (Metric.ball 0 1)`.

## Main results

* `TauCeti.Probability.circularLaw_eq_smul_restrict`: the law is `π⁻¹` times the area measure
  restricted to the disc.
* `TauCeti.Probability.isProbabilityMeasure_circularLaw`: total mass one.
* `TauCeti.Probability.ae_mem_ball_circularLaw`: the law is carried by the open unit disc.
* `TauCeti.Probability.map_rotation_circularLaw`: invariance under rotations.
* `TauCeti.Probability.integral_norm_pow_circularLaw`: `∫ ‖z‖ ^ (2 * k) = 1 / (k + 1)`.
* `TauCeti.Probability.integral_pow_circularLaw`: `∫ z ^ k = 0` for `k ≠ 0`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace TauCeti.Probability

/-- The circular law: the uniform probability measure on the open unit disc of `ℂ`. -/
def circularLaw : Measure ℂ := ProbabilityTheory.cond volume (ball 0 1)

lemma volume_ball_zero_one_complex : volume (ball (0 : ℂ) 1) = ENNReal.ofReal Real.pi := by
  simp [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

/-- The circular law is `π⁻¹` times the area measure restricted to the unit disc. -/
theorem circularLaw_eq_smul_restrict :
    circularLaw = ENNReal.ofReal Real.pi⁻¹ • volume.restrict (ball (0 : ℂ) 1) := by
  rw [circularLaw, ProbabilityTheory.cond, volume_ball_zero_one_complex,
    ENNReal.ofReal_inv_of_pos Real.pi_pos]

/-- The circular law is a probability measure. -/
instance isProbabilityMeasure_circularLaw : IsProbabilityMeasure circularLaw := by
  refine cond_isProbabilityMeasure_of_finite ?_ ?_ <;> rw [volume_ball_zero_one_complex]
  · simpa using Real.pi_pos
  · exact ENNReal.ofReal_ne_top

/-- The circular law is carried by the open unit disc. -/
theorem ae_mem_ball_circularLaw : ∀ᵐ z ∂circularLaw, z ∈ ball (0 : ℂ) 1 :=
  ae_cond_mem measurableSet_ball

/-- The circular law is invariant under rotations of the plane. -/
theorem map_rotation_circularLaw (u : Circle) :
    circularLaw.map (fun z : ℂ ↦ (u : ℂ) * z) = circularLaw := by
  have hmp : MeasurePreserving (rotation u) volume volume := (rotation u).measurePreserving
  have hpre : rotation u ⁻¹' ball (0 : ℂ) 1 = ball 0 1 := by
    ext z
    rw [mem_preimage, mem_ball_zero_iff, mem_ball_zero_iff, LinearIsometryEquiv.norm_map]
  have h := (hmp.restrict_preimage_emb (rotation u).toHomeomorph.measurableEmbedding
    (ball (0 : ℂ) 1)).map_eq
  rw [hpre] at h
  rw [circularLaw_eq_smul_restrict, Measure.map_smul]
  exacts [congrArg _ h, (measurable_const_mul _).aemeasurable]

/-- The even radial moments of the circular law: `∫ ‖z‖ ^ (2 * k) = 1 / (k + 1)`. -/
theorem integral_norm_pow_circularLaw (k : ℕ) :
    ∫ z : ℂ, ‖z‖ ^ (2 * k) ∂circularLaw = 1 / (k + 1) := by
  set f : ℝ → ℝ := (Iio 1).indicator fun r ↦ r ^ (2 * k) with hf
  have h1 : ∫ z : ℂ, ‖z‖ ^ (2 * k) ∂volume.restrict (ball (0 : ℂ) 1) = ∫ z : ℂ, f ‖z‖ := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
    by_cases hz : ‖z‖ < 1 <;> simp [hf, hz, indicator]
  have h2 := integral_fun_norm_addHaar (volume : Measure ℂ) f
  have h3 : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) • f y = 1 / (2 * k + 2) := by
    have : ∀ y : ℝ, y ^ (Module.finrank ℝ ℂ - 1) • f y =
        (Iio 1).indicator (fun y : ℝ ↦ y ^ (2 * k + 1)) y := by
      intro y
      by_cases hy : y < 1 <;> simp [hf, hy, indicator, pow_succ, mul_comm]
    simp_rw [this]
    rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
      show Iio (1 : ℝ) ∩ Ioi 0 = Ioo 0 1 by ext; simp [and_comm],
      ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_pow]
    push_cast
    field_simp
    ring
  rw [circularLaw_eq_smul_restrict, integral_smul_measure, h1, h2, h3]
  simp only [Complex.finrank_real_complex, Measure.real, volume_ball_zero_one_complex,
    ENNReal.toReal_ofReal Real.pi_pos.le, smul_eq_mul, nsmul_eq_mul, ENNReal.toReal_ofReal
      (inv_nonneg.2 Real.pi_pos.le)]
  push_cast
  field_simp

/-- Every nonzero natural power of `z` integrates to zero against the circular law. -/
theorem integral_pow_circularLaw {k : ℕ} (hk : k ≠ 0) : ∫ z, z ^ k ∂circularLaw = 0 := by
  set u : Circle := Circle.exp (Real.pi / k) with hu
  have huk : (u : ℂ) ^ k = -1 := by
    rw [hu, Circle.coe_exp, ← Complex.exp_nat_mul]
    have : (k : ℂ) * (↑(Real.pi / k) * Complex.I) = Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [this, Complex.exp_pi_mul_I]
  have h := integral_map (μ := circularLaw) (measurable_const_mul (u : ℂ)).aemeasurable
    (f := fun z : ℂ ↦ z ^ k) (by fun_prop)
  rw [map_rotation_circularLaw] at h
  simp only [mul_pow, huk, neg_one_mul, integral_neg] at h
  linear_combination (1 / 2 : ℂ) * h

end TauCeti.Probability
