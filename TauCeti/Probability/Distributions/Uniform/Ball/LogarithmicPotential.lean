/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.LogarithmicPotential.Basic
public import TauCeti.Probability.Distributions.Uniform.Ball.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Analysis.SpecialFunctions.Integrals.LogPower
import TauCeti.MeasureTheory.Integral.PolarCoord
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The logarithmic potential of the uniform law on a disc

Let `c : ℂ` and `r > 0`. The uniform probability measure on the disc of center `c` and radius `r`
has logarithmic potential `U(z) = ∫ log ‖z - w‖`, with respect to that measure, equal to

* `log ‖z - c‖` for `r ≤ ‖z - c‖`, the potential of the point mass at `c`;
* `log r + (‖z - c‖ ^ 2 / r ^ 2 - 1) / 2` for `‖z - c‖ < r`, a quadratic function of the
  distance to the center.

The kernel `w ↦ log ‖z - w‖` is integrable against the law at every point `z`, so these formulas
hold everywhere, not only for almost every `z`. For `c = 0` and `r = 1` the law is the circular law,
and these formulas are the limiting potential against which the potentials of random eigenvalue
distributions are compared to prove weak convergence to it.

## Main results

* `TauCeti.Probability.integrable_log_norm_sub_uniformBallMeasure`: the logarithmic kernel is
  integrable against the uniform law on a disc.
* `TauCeti.Probability.logarithmicPotential_uniformBallMeasure_of_le_norm_sub`: the potential
  outside the open disc.
* `TauCeti.Probability.logarithmicPotential_uniformBallMeasure_of_norm_sub_lt`: the potential
  inside the disc.

## Implementation notes

The computation uses polar coordinates about `c`. By Jensen's formula, the average of
`log ‖z - w‖` over the circle of radius `ρ` about `c` is `log (max ρ ‖z - c‖)`; this is Mathlib's
`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`. What remains is the radial integral
`2 / r ^ 2 * ∫ ρ in 0..r, ρ * log (max ρ ‖z - c‖)`.

## References

* C. Bordenave, D. Chafaï, *Around the circular law*, Probab. Surveys 9 (2012), §4.1, (4.2),
  where the potential is defined with the opposite sign.
-/

public section

noncomputable section

open MeasureTheory Metric Set Real
open scoped ENNReal

namespace TauCeti.Probability

/-- For every `z : ℂ`, the logarithmic kernel `w ↦ log ‖z - w‖` is integrable against the uniform
law on a disc of any radius, so the logarithmic potential of the law is a genuine integral at every
point. -/
theorem integrable_log_norm_sub_uniformBallMeasure (c z : ℂ) (r : ℝ) :
    Integrable (fun w ↦ log ‖z - w‖) (uniformBallMeasure c r) := by
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · simp [uniformBallMeasure_of_neg hr]
  · simpa using integrable_dirac (f := fun w ↦ log ‖z - w‖) (by simp)
  -- The kernel is a reflected translate of the locally integrable `log ‖·‖`.
  have hK : IntegrableOn (fun x : ℂ ↦ log ‖x‖) (closedBall (z - c) r) :=
    locallyIntegrable_log_norm.integrableOn_isCompact (isCompact_closedBall _ _)
  have hpre : (fun w ↦ z - w) ⁻¹' closedBall (z - c) r = closedBall c r := by
    ext w
    simp [dist_eq_norm, norm_sub_rev]
  have hcl : IntegrableOn (fun w ↦ log ‖z - w‖) (closedBall c r) := by
    rw [← hpre]
    exact ((volume.measurePreserving_sub_left z).integrableOn_comp_preimage
      (Homeomorph.subLeft z).measurableEmbedding).2 hK
  rw [uniformBallMeasure_of_ne_zero hr.ne', ProbabilityTheory.cond]
  exact (hcl.mono_set ball_subset_closedBall).smul_measure
    (ENNReal.inv_ne_top.2 (measure_ball_pos volume c hr).ne')

/-- The logarithmic potential of the uniform law on a disc of radius `r > 0` as the radial
integral `2 / r ^ 2 * ∫ ρ in 0..r, ρ * log (max ρ ‖z - c‖)`. -/
private theorem logarithmicPotential_uniformBallMeasure_eq_integral (c z : ℂ) {r : ℝ}
    (hr : 0 < r) :
    (uniformBallMeasure c r).logarithmicPotential z =
      2 / r ^ 2 * ∫ ρ in 0..r, ρ * log (max ρ ‖z - c‖) := by
  have hint := integrable_log_norm_sub_uniformBallMeasure c z r
  rw [uniformBallMeasure_of_ne_zero hr.ne', ProbabilityTheory.cond,
    integrable_smul_measure (ENNReal.inv_ne_zero.2 measure_ball_lt_top.ne)
      (ENNReal.inv_ne_top.2 (measure_ball_pos volume c hr).ne')] at hint
  have hball : IntegrableOn (fun w ↦ log ‖z - w‖) (ball c r) := hint
  have hset : {w : ℂ | 0 ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r} = closedBall c r := by
    ext w
    simp [dist_eq_norm]
  have hcl : IntegrableOn (fun w ↦ log ‖z - w‖) {w : ℂ | 0 ≤ ‖w - c‖ ∧ ‖w - c‖ ≤ r} :=
    hset ▸ hball.congr_set_ae (volume.addHaar_closedBall_ae_eq_ball c r)
  -- Integrate over the closed disc in polar coordinates about `c`.
  have hpolar : ∫ w in ball c r, log ‖z - w‖ =
      2 * π * ∫ ρ in 0..r, ρ * log (max ρ ‖z - c‖) := by
    rw [← setIntegral_congr_set (volume.addHaar_closedBall_ae_eq_ball c r), ← hset,
      integral_annulus_eq_integral_circleMap le_rfl hr.le hcl,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun ρ hρ ↦ ?_
    rcases (uIcc_of_le hr.le ▸ hρ).1.eq_or_lt with rfl | hρ0
    · simp
    -- Jensen's formula for the circle average, moved from `[0, 2π]` to `[-π, π]`.
    have hper : (fun θ ↦ log ‖z - circleMap c ρ θ‖).Periodic (2 * π) :=
      fun θ ↦ by simp [periodic_circleMap c ρ θ]
    have havg := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (c := c) (a := z)
      hρ0.ne'
    rw [circleAverage_def, smul_eq_mul] at havg
    have hcircle : ∫ θ in -π..π, log ‖z - circleMap c ρ θ‖ =
        2 * π * (log ρ + log⁺ (ρ⁻¹ * ‖c - z‖)) := by
      rw [← havg, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      have h := hper.intervalIntegral_add_eq (-π) 0
      rw [show -π + 2 * π = π by ring, zero_add] at h
      simp_rw [h, norm_sub_rev z]
    have hmax : log ρ + log⁺ (ρ⁻¹ * ‖c - z‖) = log (max ρ ‖z - c‖) := by
      rw [posLog_eq_log_max_one (by positivity), ← log_mul hρ0.ne' (by positivity),
        mul_max_of_nonneg _ _ hρ0.le, mul_one, mul_inv_cancel_left₀ hρ0.ne', norm_sub_rev]
    rw [hcircle, hmax, smul_eq_mul]
    ring
  rw [Measure.logarithmicPotential_def, uniformBallMeasure_of_ne_zero hr.ne',
    ProbabilityTheory.cond, integral_smul_measure, hpolar, Complex.volume_ball,
    ENNReal.toReal_inv, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
    ENNReal.coe_toReal, NNReal.coe_real_pi, smul_eq_mul]
  field_simp

/-- **The logarithmic potential of the uniform law on a disc, outside the disc.** For a radius
`r ≥ 0` and a point `z` at distance at least `r` from the center `c`, the potential is
`log ‖z - c‖`: on the logarithmic kernel the law acts like the point mass at its center. -/
theorem logarithmicPotential_uniformBallMeasure_of_le_norm_sub (c : ℂ) {r : ℝ} {z : ℂ}
    (hr : 0 ≤ r) (hz : r ≤ ‖z - c‖) :
    (uniformBallMeasure c r).logarithmicPotential z = log ‖z - c‖ := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  rw [logarithmicPotential_uniformBallMeasure_eq_integral c z hr,
    intervalIntegral.integral_congr (g := fun ρ ↦ ρ * log ‖z - c‖) fun ρ hρ ↦ ?_,
    intervalIntegral.integral_mul_const, integral_id]
  · field_simp
    ring
  · rw [uIcc_of_le hr.le] at hρ
    simp only [max_eq_right (hρ.2.trans hz)]

/-- **The logarithmic potential of the uniform law on a disc, inside the disc.** For a point `z`
at distance less than `r` from the center `c`, the potential is
`log r + (‖z - c‖ ^ 2 / r ^ 2 - 1) / 2`. -/
theorem logarithmicPotential_uniformBallMeasure_of_norm_sub_lt (c : ℂ) {r : ℝ} {z : ℂ}
    (hz : ‖z - c‖ < r) :
    (uniformBallMeasure c r).logarithmicPotential z =
      log r + (‖z - c‖ ^ 2 / r ^ 2 - 1) / 2 := by
  set d := ‖z - c‖
  have hd0 : 0 ≤ d := norm_nonneg _
  have hr : 0 < r := hd0.trans_lt hz
  -- Split the radial integral at the distance `d`, where the circles start enclosing `z`.
  have h₁ : EqOn (fun ρ ↦ ρ * log (max ρ d)) (fun ρ ↦ ρ * log d) (uIcc 0 d) := by
    intro ρ hρ
    rw [uIcc_of_le hd0] at hρ
    simp only [max_eq_right hρ.2]
  have h₂ : EqOn (fun ρ ↦ ρ * log (max ρ d)) (fun ρ ↦ ρ * log ρ) (uIcc d r) := by
    intro ρ hρ
    rw [uIcc_of_le hz.le] at hρ
    simp only [max_eq_left hρ.1]
  have hi₁ : IntervalIntegrable (fun ρ ↦ ρ * log (max ρ d)) volume 0 d :=
    (intervalIntegrable_congr (h₁.mono uIoc_subset_uIcc)).2
      ((continuous_id.mul continuous_const).intervalIntegrable 0 d)
  have hi₂ : IntervalIntegrable (fun ρ ↦ ρ * log (max ρ d)) volume d r :=
    (intervalIntegrable_congr (h₂.mono uIoc_subset_uIcc)).2
      (continuous_mul_log.intervalIntegrable d r)
  rw [logarithmicPotential_uniformBallMeasure_eq_integral c z hr,
    ← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂,
    intervalIntegral.integral_congr h₁, intervalIntegral.integral_congr h₂,
    intervalIntegral.integral_mul_const, integral_id, TauCeti.integral_mul_log]
  field_simp
  ring

end TauCeti.Probability
