/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic
public import TauCeti.Analysis.SpecialFunctions.Beta
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Even moments of the Japanese bracket

This file computes the even radial moments of the integrable powers of the Japanese bracket on a
finite-dimensional real inner product space.  If `d = finrank ℝ V` and `d + 2m < r`, then

`integral x, (‖x‖²)^m (1 + ‖x‖²)^(-r/2)`

is a beta integral.  The condition records the decay needed at infinity; even powers have no
additional singularity at the origin.  These formulas are useful for rescaled Euclidean profiles,
including the moments of the Yamabe bubbles.

## Main declarations

* `TauCeti.integrable_norm_sq_pow_mul_rpow_neg_one_add_norm_sq`: integrability of every
  subcritical even moment.
* `TauCeti.integral_norm_sq_pow_mul_rpow_neg_one_add_norm_sq`: its value, for any additive Haar
  measure, in terms of Euler's beta function and the measure of the unit ball.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §3.
-/

public section

namespace TauCeti

open MeasureTheory Metric Module ProbabilityTheory Real Set

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The `2m`-th radial moment of the Japanese bracket power is integrable when its decay exponent
exceeds `dim V + 2m`. -/
theorem integrable_norm_sq_pow_mul_rpow_neg_one_add_norm_sq (μ : Measure V) [μ.IsAddHaarMeasure]
    (m : ℕ) {r : ℝ}
    (hr : (finrank ℝ V : ℝ) + 2 * m < r) :
    Integrable (fun x : V ↦ (‖x‖ ^ 2) ^ m * (1 + ‖x‖ ^ 2) ^ (-r / 2)) μ := by
  have hdecay : (finrank ℝ V : ℝ) < r - 2 * m := by linarith
  have hmajorant := integrable_rpow_neg_one_add_norm_sq (E := V) (μ := μ) hdecay
  refine hmajorant.mono' (by fun_prop) (.of_forall fun x ↦ ?_)
  have hA : 0 < 1 + ‖x‖ ^ 2 := by positivity
  have hpow : (‖x‖ ^ 2) ^ m ≤ (1 + ‖x‖ ^ 2) ^ m := by
    gcongr
    linarith
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hA.le _))]
  calc
    (‖x‖ ^ 2) ^ m * (1 + ‖x‖ ^ 2) ^ (-r / 2)
        ≤ (1 + ‖x‖ ^ 2) ^ m * (1 + ‖x‖ ^ 2) ^ (-r / 2) := by gcongr
    _ = (1 + ‖x‖ ^ 2) ^ (-(r - 2 * m) / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hA]
      congr 1
      ring

/-- The `2m`-th radial moment of the Japanese bracket power, for an additive Haar measure `μ`.
For Lebesgue measure the factor `dim V * volume.real (ball 0 1)` is the area of the unit sphere in
`V`. -/
theorem integral_norm_sq_pow_mul_rpow_neg_one_add_norm_sq [Nontrivial V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (m : ℕ) {r : ℝ} (hr : (finrank ℝ V : ℝ) + 2 * m < r) :
    ∫ x : V, (‖x‖ ^ 2) ^ m * (1 + ‖x‖ ^ 2) ^ (-r / 2) ∂μ =
      (finrank ℝ V : ℝ) * μ.real (ball (0 : V) 1) *
        (beta (((finrank ℝ V : ℝ) + 2 * m) / 2)
          ((r - finrank ℝ V - 2 * m) / 2) / 2) := by
  set d := finrank ℝ V with hd
  have hd0 : 0 < d := finrank_pos
  -- In polar coordinates the moment is the radial beta integral with `s = d + 2m`.
  have hrad :
      ∫ y in Ioi (0 : ℝ), y ^ (d - 1) • ((y ^ 2) ^ m * (1 + y ^ 2) ^ (-r / 2)) =
        beta (((d : ℝ) + 2 * m) / 2) ((r - d - 2 * m) / 2) / 2 := by
    rw [show r - d - 2 * m = r - (d + 2 * m) by ring,
      ← integral_rpow_mul_one_add_sq_rpow (by positivity) hr]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
    have hpow : y ^ ((d : ℝ) + 2 * m - 1) = y ^ (d - 1) * (y ^ 2) ^ m := by
      rw [show (d : ℝ) + 2 * m - 1 = ((d - 1 + 2 * m : ℕ) : ℝ) by
        push_cast [Nat.cast_sub hd0]; ring, Real.rpow_natCast]
      ring
    rw [smul_eq_mul, hpow]
    ring
  rw [integral_fun_norm_addHaar μ
    (fun y : ℝ ↦ (y ^ 2) ^ m * (1 + y ^ 2) ^ (-r / 2)), hrad, nsmul_eq_mul,
    smul_eq_mul, ← hd]
  ring

end TauCeti
