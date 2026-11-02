/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import TauCeti.Probability.Distributions.Uniform.Ball.Basic

/-!
# The circular law

The circular law is the uniform probability measure on the open unit disc of `ℂ`, with density
`π⁻¹ 1_{|z| < 1}` with respect to the area measure. It is the uniform ball law
`TauCeti.Probability.uniformBallMeasure` of the plane `ℂ`, of center `0` and radius `1`.

## Main definitions

* `TauCeti.Probability.circularLaw`: the uniform probability measure on the unit disc,
  `uniformBallMeasure 0 1`.

## Main results

* `TauCeti.Probability.circularLaw_eq_smul_restrict`: the law is `π⁻¹` times the area measure
  restricted to the disc.
* `TauCeti.Probability.isProbabilityMeasure_circularLaw`: total mass one.
* `TauCeti.Probability.ae_mem_ball_circularLaw`: the law is carried by the open unit disc.
* `TauCeti.Probability.map_rotation_circularLaw`: invariance under rotations.
* `TauCeti.Probability.integral_norm_pow_circularLaw`: `∫ ‖z‖ ^ n = 2 / (n + 2)`.
* `TauCeti.Probability.integral_pow_circularLaw`: `∫ z ^ k = 0` for `k ≠ 0`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace TauCeti.Probability

/-- The circular law: the uniform probability measure on the open unit disc of `ℂ`. -/
def circularLaw : Measure ℂ := uniformBallMeasure 0 1

theorem circularLaw_def : circularLaw = uniformBallMeasure (0 : ℂ) 1 := (rfl)

/-- The circular law is `π⁻¹` times the area measure restricted to the unit disc. -/
theorem circularLaw_eq_smul_restrict :
    circularLaw = ENNReal.ofReal Real.pi⁻¹ • volume.restrict (ball (0 : ℂ) 1) := by
  have hvol : volume (ball (0 : ℂ) 1) = ENNReal.ofReal Real.pi := by
    simp [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [circularLaw_def, uniformBallMeasure_of_ne_zero one_ne_zero, ProbabilityTheory.cond, hvol,
    ENNReal.ofReal_inv_of_pos Real.pi_pos]

/-- The circular law is a probability measure. -/
instance isProbabilityMeasure_circularLaw : IsProbabilityMeasure circularLaw :=
  isProbabilityMeasure_uniformBallMeasure zero_le_one

/-- The circular law is carried by the open unit disc. -/
theorem ae_mem_ball_circularLaw : ∀ᵐ z ∂circularLaw, z ∈ ball (0 : ℂ) 1 :=
  ae_mem_ball_uniformBallMeasure one_pos

/-- The circular law is invariant under rotations of the plane. -/
theorem map_rotation_circularLaw (u : Circle) :
    circularLaw.map (fun z : ℂ ↦ (u : ℂ) * z) = circularLaw := by
  have hfun : ⇑(rotation u) = fun z : ℂ ↦ (u : ℂ) * z := funext (rotation_apply u)
  have h := (rotation u).map_uniformBallMeasure (0 : ℂ) 1
  rw [map_zero, hfun] at h
  exact h

/-- The radial moments of the circular law: `∫ ‖z‖ ^ n = 2 / (n + 2)`. -/
@[simp]
theorem integral_norm_pow_circularLaw (n : ℕ) :
    ∫ z : ℂ, ‖z‖ ^ n ∂circularLaw = 2 / (n + 2) := by
  have hmap := map_norm_sub_div_uniformBallMeasure (0 : ℂ) (r := 1) one_pos
  rw [Complex.finrank_real_complex] at hmap
  have h := integral_map (μ := uniformBallMeasure (0 : ℂ) 1)
    (φ := fun x : ℂ ↦ ‖x - 0‖ / 1) (f := fun t : ℝ ↦ t ^ n) (by fun_prop) (by fun_prop)
  rw [hmap] at h
  have hb := integral_pow_betaMeasure (α := ((2 : ℕ) : ℝ)) (β := 1) (by norm_num) one_pos n
  rw [circularLaw_def]
  simp only [sub_zero, div_one] at h
  rw [← h, hb]
  have h2n : 0 < Real.Gamma (2 + n) := Real.Gamma_pos_of_pos (by positivity)
  have h3 : Real.Gamma (2 + 1 + n) = (2 + n) * Real.Gamma (2 + n) := by
    rw [show (2 : ℝ) + 1 + n = (2 + n) + 1 by ring, Real.Gamma_add_one (by positivity)]
  have h4 : Real.Gamma (2 + 1) = 2 := by
    rw [Real.Gamma_add_one two_ne_zero, Real.Gamma_two, mul_one]
  push_cast
  rw [h3, h4, Real.Gamma_two]
  field_simp
  ring

/-- Every nonzero natural power of `z` integrates to zero against the circular law. -/
@[simp]
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
