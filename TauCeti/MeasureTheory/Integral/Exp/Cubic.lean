/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Laplace-type integrals with cubic decay

For real `q > -1` and `b > 0` and every complex `z`, the kernel
`t ↦ t ^ q * exp (z t - b t³)` is Bochner integrable on `(0, ∞)`: its norm is
`t ^ q * exp (Re z * t - b t³)`, and the cubic term dominates every linear growth. Differentiating
under the integral sign, the integral `∫₀^∞ t ^ q exp (z t - b t³) dt` is an entire function of
`z` whose derivative is the moment of order `q + 1`.

Integrals of this shape represent the Scorer function `Hi` (`b = 1/3`, `q = 0`) and the sum of
squares `Ai² + Bi²` of the Airy functions (`b = 1/12`, `q = -1/2`).

## Main results

* `TauCeti.norm_cpow_mul_cexp_mul_sub_mul_cube`: the norm of the kernel.
* `TauCeti.integrableOn_cpow_mul_cexp_mul_sub_mul_cube`: integrability on `(0, ∞)`.
* `TauCeti.hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_cube`: the derivative in `z` of the
  integral is the integral of the kernel with `q` replaced by `q + 1`.
-/

public section

noncomputable section

open Complex MeasureTheory Set

namespace TauCeti

/-- For `0 < t`, the norm of `t ^ q * exp (z t - b t³)` is `t ^ q * exp (Re z * t - b t³)`. -/
theorem norm_cpow_mul_cexp_mul_sub_mul_cube {t : ℝ} (ht : 0 < t) (q b : ℝ) (z : ℂ) :
    ‖(t : ℂ) ^ (q : ℂ) * cexp (z * t - b * (t : ℂ) ^ 3)‖ =
      t ^ q * Real.exp (z.re * t - b * t ^ (3 : ℝ)) := by
  have hcube : (b : ℂ) * (t : ℂ) ^ 3 = ((b * t ^ 3 : ℝ) : ℂ) := by push_cast; ring
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, ofReal_re, Complex.norm_exp, hcube,
    sub_re, ofReal_re, re_mul_ofReal, Real.rpow_ofNat]

/-- For real `q > -1` and `b > 0` and every complex `z`, the kernel `t ↦ t ^ q * exp (z t - b t³)`
is Bochner integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_mul_cexp_mul_sub_mul_cube {q b : ℝ} (hq : -1 < q) (hb : 0 < b)
    (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (q : ℂ) * cexp (z * t - b * (t : ℂ) ^ 3)) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (q : ℂ) * cexp (z * t - b * (t : ℂ) ^ 3))
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    exact ((continuousAt_ofReal_cpow_const t q (Or.inr ht.ne')).mul
      (by fun_prop)).continuousWithinAt
  refine (integrableOn_rpow_mul_exp_mul_sub_mul_rpow (p := 3) (by norm_num) hq hb z.re).mono'
    hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_cpow_mul_cexp_mul_sub_mul_cube ht]

/-- For real `q > -1` and `b > 0`, the derivative of `w ↦ ∫₀^∞ t ^ q exp (w t - b t³) dt` at `z`
is `∫₀^∞ t ^ (q + 1) exp (z t - b t³) dt`. -/
theorem hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_cube {q b : ℝ} (hq : -1 < q) (hb : 0 < b)
    (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q : ℂ) * cexp (w * t - b * (t : ℂ) ^ 3))
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((q : ℂ) + 1) * cexp (z * t - b * (t : ℂ) ^ 3)) z := by
  have hq1 : -1 < q + 1 := by linarith
  -- The kernel of order `q + 1`, written with a real exponent.
  have hcast : ((q + 1 : ℝ) : ℂ) = (q : ℂ) + 1 := by push_cast; ring
  have hint1 := integrableOn_cpow_mul_cexp_mul_sub_mul_cube hq1 hb z
  rw [hcast] at hint1
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun w (t : ℝ) => (t : ℂ) ^ ((q : ℂ) + 1) * cexp (w * t - b * (t : ℂ) ^ 3))
    (bound := fun t => t ^ (q + 1) * Real.exp ((‖z‖ + 1) * t - b * t ^ (3 : ℝ)))
    (Metric.ball_mem_nhds z zero_lt_one)
    (.of_forall fun w => (integrableOn_cpow_mul_cexp_mul_sub_mul_cube hq hb w).1)
    (integrableOn_cpow_mul_cexp_mul_sub_mul_cube hq hb z) hint1.1 ?_
    (integrableOn_rpow_mul_exp_mul_sub_mul_rpow (p := 3) (by norm_num) hq1 hb (‖z‖ + 1)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
    have hw_re : w.re ≤ ‖z‖ + 1 := by
      have hdist : ‖w - z‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hw
      exact (Complex.re_le_norm w).trans (by linarith [norm_sub_rev w z, norm_sub_norm_le w z])
    rw [← hcast, norm_cpow_mul_cexp_mul_sub_mul_cube ht]
    gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w _
    have hd := (((hasDerivAt_id w).mul_const (t : ℂ)).sub_const
      ((b : ℂ) * (t : ℂ) ^ 3)).cexp.const_mul ((t : ℂ) ^ (q : ℂ))
    refine hd.congr_deriv ?_
    rw [cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_one, id]
    ring

end TauCeti
