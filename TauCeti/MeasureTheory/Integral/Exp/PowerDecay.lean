/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Gamma
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Laplace-type integrals with superlinear power decay

For real `p > 1`, `q > -1` and `b > 0` and every complex `z`, the kernel
`t ↦ t ^ q * exp (z t - b t ^ p)` is Bochner integrable on `(0, ∞)`: its norm is
`t ^ q * exp (Re z * t - b t ^ p)`, and the power `t ^ p` dominates every linear growth.
Differentiating under the integral sign, the integral `∫₀^∞ t ^ q exp (z t - b t ^ p) dt` is an
entire function of `z` whose derivative is the moment of order `q + 1`. For every real `q` the
kernel tends to zero at infinity, and at `z = 0` the integral is a Gamma value,
`∫₀^∞ t ^ q exp (-b t ^ p) dt = b ^ (-(q + 1) / p) Γ((q + 1) / p) / p` (this holds for `p > 0`).

With `p = 3`, integrals of this shape represent the Scorer function `Hi`, which is `π⁻¹` times
the integral with `b = 1/3` and `q = 0`, and the sum of squares `Ai² + Bi²` of the Airy
functions, which is `π^{-3/2}` times the integral with `b = 1/12` and `q = -1/2`.

## Main results

* `TauCeti.norm_cpow_mul_cexp_mul_sub_mul_rpow`: the norm of the kernel.
* `TauCeti.integrableOn_cpow_mul_cexp_mul_sub_mul_rpow`: integrability on `(0, ∞)`.
* `TauCeti.hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_rpow`: the derivative in `z` of the
  integral is the integral of the kernel with `q` replaced by `q + 1`.
* `TauCeti.tendsto_cpow_mul_cexp_mul_sub_mul_rpow_atTop`: the kernel tends to zero at infinity.
* `TauCeti.integral_cpow_mul_cexp_neg_mul_rpow`: the Gamma value of the integral at `z = 0`.

The norm, integrability and differentiation arguments are extracted and generalized from the
proofs for the integral of `Ai² + Bi²` in `TauCeti.Analysis.SpecialFunctions.Airy.ProductIntegral`
(formerly its own dominated-differentiation proof of
`TauCeti.hasDerivAt_integral_pow_mul_cexp_sub_cube_div_twelve_mul_cpow`); the Gamma value is the
complex form of Mathlib's `integral_rpow_mul_exp_neg_mul_rpow`.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace TauCeti

/-- For `0 < t`, the norm of `t ^ q * exp (z t - b t ^ p)` is
`t ^ q * exp (Re z * t - b t ^ p)`. -/
theorem norm_cpow_mul_cexp_mul_sub_mul_rpow {t : ℝ} (ht : 0 < t) (q b p : ℝ) (z : ℂ) :
    ‖(t : ℂ) ^ (q : ℂ) * cexp (z * t - ((b * t ^ p : ℝ) : ℂ))‖ =
      t ^ q * Real.exp (z.re * t - b * t ^ p) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, ofReal_re, Complex.norm_exp, sub_re,
    ofReal_re, re_mul_ofReal]

/-- For real `p > 1`, `q > -1` and `b > 0` and every complex `z`, the kernel
`t ↦ t ^ q * exp (z t - b t ^ p)` is Bochner integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_mul_cexp_mul_sub_mul_rpow {p q b : ℝ} (hp : 1 < p) (hq : -1 < q)
    (hb : 0 < b) (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (q : ℂ) * cexp (z * t - ((b * t ^ p : ℝ) : ℂ)))
      (Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (q : ℂ) * cexp (z * t - ((b * t ^ p : ℝ) : ℂ)))
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    exact ((continuousAt_ofReal_cpow_const t q (Or.inr ht.ne')).mul
      (by fun_prop)).continuousWithinAt
  refine (integrableOn_rpow_mul_exp_mul_sub_mul_rpow hp hq hb z.re).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_cpow_mul_cexp_mul_sub_mul_rpow ht]

/-- For real `p > 1`, `q > -1` and `b > 0`, the derivative of
`w ↦ ∫₀^∞ t ^ q exp (w t - b t ^ p) dt` at `z` is `∫₀^∞ t ^ (q + 1) exp (z t - b t ^ p) dt`. -/
theorem hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_rpow {p q b : ℝ} (hp : 1 < p)
    (hq : -1 < q) (hb : 0 < b) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q : ℂ) * cexp (w * t - ((b * t ^ p : ℝ) : ℂ)))
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((q : ℂ) + 1) * cexp (z * t - ((b * t ^ p : ℝ) : ℂ))) z := by
  have hq1 : -1 < q + 1 := by linarith
  -- The kernel of order `q + 1`, written with a real exponent.
  have hcast : ((q + 1 : ℝ) : ℂ) = (q : ℂ) + 1 := by push_cast; ring
  have hint1 := integrableOn_cpow_mul_cexp_mul_sub_mul_rpow hp hq1 hb z
  rw [hcast] at hint1
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun w (t : ℝ) => (t : ℂ) ^ ((q : ℂ) + 1) * cexp (w * t - ((b * t ^ p : ℝ) : ℂ)))
    (bound := fun t => t ^ (q + 1) * Real.exp ((‖z‖ + 1) * t - b * t ^ p))
    (Metric.ball_mem_nhds z zero_lt_one)
    (.of_forall fun w => (integrableOn_cpow_mul_cexp_mul_sub_mul_rpow hp hq hb w).1)
    (integrableOn_cpow_mul_cexp_mul_sub_mul_rpow hp hq hb z) hint1.1 ?_
    (integrableOn_rpow_mul_exp_mul_sub_mul_rpow hp hq1 hb (‖z‖ + 1)) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
    have hw_re : w.re ≤ ‖z‖ + 1 := by
      have hdist : ‖w - z‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hw
      exact (Complex.re_le_norm w).trans (by linarith [norm_sub_rev w z, norm_sub_norm_le w z])
    rw [← hcast, norm_cpow_mul_cexp_mul_sub_mul_rpow ht]
    gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w _
    have hd := (((hasDerivAt_id w).mul_const (t : ℂ)).sub_const
      ((b * t ^ p : ℝ) : ℂ)).cexp.const_mul ((t : ℂ) ^ (q : ℂ))
    refine hd.congr_deriv ?_
    rw [cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_one, id]
    ring

/-- For real `p > 1` and `b > 0`, every real `q` and every complex `z`, the kernel
`t ↦ t ^ q * exp (z t - b t ^ p)` tends to zero at infinity. -/
theorem tendsto_cpow_mul_cexp_mul_sub_mul_rpow_atTop {p q b : ℝ} (hp : 1 < p) (hb : 0 < b)
    (z : ℂ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (q : ℂ) * cexp (z * t - ((b * t ^ p : ℝ) : ℂ))) atTop
      (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  -- The exponent `(Re z + 1) t - b t ^ p = t (Re z + 1 - b t ^ (p - 1))` tends to `-∞`.
  have hpoly : Tendsto (fun t : ℝ => (z.re + 1) * t - b * t ^ p) atTop atBot := by
    have hlin : Tendsto (fun t : ℝ => z.re + 1 - b * t ^ (p - 1)) atTop atBot :=
      tendsto_atBot_add_const_left _ _ (tendsto_neg_atTop_atBot.comp
        ((tendsto_rpow_atTop (sub_pos.mpr hp)).const_mul_atTop hb))
    refine (tendsto_id.atTop_mul_atBot₀ hlin).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [id, Real.rpow_sub_one ht.ne']
    field_simp
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero q 1 one_pos).mul
    (Real.tendsto_exp_atBot.comp hpoly)
  rw [zero_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Function.comp_apply, norm_cpow_mul_cexp_mul_sub_mul_rpow ht, mul_assoc, ← Real.exp_add]
  ring_nf

/-- For real `p > 0`, `q > -1` and `b > 0`, the kernel at `z = 0` integrates to a Gamma value:
`∫₀^∞ t ^ q exp (-b t ^ p) dt = b ^ (-(q + 1) / p) (1 / p) Γ((q + 1) / p)`. -/
theorem integral_cpow_mul_cexp_neg_mul_rpow {p q b : ℝ} (hp : 0 < p) (hq : -1 < q) (hb : 0 < b) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q : ℂ) * cexp (-((b * t ^ p : ℝ) : ℂ)) =
      ((b ^ (-(q + 1) / p) * (1 / p) * Real.Gamma ((q + 1) / p) : ℝ) : ℂ) := by
  rw [← integral_rpow_mul_exp_neg_mul_rpow hp hq hb, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
  rw [← ofReal_cpow ht.le, ← ofReal_neg, ← ofReal_exp, ← ofReal_mul, neg_mul]

end TauCeti
