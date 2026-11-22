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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Moments.ComplexMGF
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
proofs for the integral of `Ai² + Bi²` in `TauCeti.Analysis.SpecialFunctions.Airy.Product.Integral`
(formerly its own dominated-differentiation proof of
`TauCeti.hasDerivAt_integral_pow_mul_cexp_sub_cube_div_twelve_mul_cpow`). The derivative is
Mathlib's `ProbabilityTheory.hasDerivAt_integral_pow_mul_exp` for the measure with density
`t ^ q exp (-b t ^ p)` on `(0, ∞)`; the Gamma value is the complex form of Mathlib's
`integral_rpow_mul_exp_neg_mul_rpow`.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology NNReal ENNReal

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
  -- The weight `t ^ q exp (-b t ^ p)` as a density on `(0, ∞)`; the kernel integrals are
  -- the exponential moments of the identity against it, so Mathlib's moment derivative applies.
  set ρ : ℝ → ℝ≥0 := fun t => Real.toNNReal (t ^ q * Real.exp (-(b * t ^ p))) with hρ
  have hρm : Measurable ρ := by fun_prop
  set μ := (volume.restrict (Ioi (0 : ℝ))).withDensity fun t => (ρ t : ℝ≥0∞)
  have hconv : ∀ (n : ℕ) (w : ℂ), ∫ t, (t : ℂ) ^ n * cexp (w * t) ∂μ =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((q : ℂ) + n) * cexp (w * t - ((b * t ^ p : ℝ) : ℂ)) := by
    intro n w
    rw [integral_withDensity_eq_integral_smul hρm]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [hρ, NNReal.smul_def, Real.coe_toNNReal _ (by positivity), real_smul,
      cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_natCast, ← ofReal_cpow ht.le, sub_eq_add_neg,
      Complex.exp_add, ← ofReal_neg, ← ofReal_exp, ofReal_mul]
    ring
  have hexp : ∀ s : ℝ, s ∈ ProbabilityTheory.integrableExpSet id μ := by
    intro s
    refine (integrable_withDensity_iff_integrable_smul hρm).2 ?_
    refine (integrableOn_rpow_mul_exp_mul_sub_mul_rpow hp hq hb s).congr_fun
      (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    rw [hρ, NNReal.smul_def, Real.coe_toNNReal _ (by positivity), smul_eq_mul, id, mul_assoc,
      ← Real.exp_add]
    ring_nf
  have hz : z.re ∈ interior (ProbabilityTheory.integrableExpSet id μ) := by
    rw [eq_univ_of_forall hexp, interior_univ]
    trivial
  have h := ProbabilityTheory.hasDerivAt_integral_pow_mul_exp hz 0
  simp only [id] at h
  rw [funext (hconv 0), hconv 1 z] at h
  simpa only [Nat.cast_zero, add_zero, Nat.cast_one] using h

/-- For real `p > 1` and `b > 0`, every real `q` and every complex `z`, the kernel
`t ↦ t ^ q * exp (z t - b t ^ p)` tends to zero at infinity. -/
theorem tendsto_cpow_mul_cexp_mul_sub_mul_rpow_atTop {p q b : ℝ} (hp : 1 < p) (hb : 0 < b)
    (z : ℂ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ (q : ℂ) * cexp (z * t - ((b * t ^ p : ℝ) : ℂ))) atTop
      (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  -- The exponent `(Re z + 1) t - b t ^ p` tends to `-∞`: with `d = max 1 (Re z + 1)`, it is at
  -- most `d t - b t ^ p = -d ((b / d) t ^ p - t)`, and `exp (-(b / d) t ^ p) = o(exp (-t))`.
  have hpoly : Tendsto (fun t : ℝ => (z.re + 1) * t - b * t ^ p) atTop atBot := by
    set d := max 1 (z.re + 1)
    have hd : 0 < d := lt_max_of_lt_left one_pos
    have h := (Real.isLittleO_exp_comp_exp_comp.1
      (exp_neg_mul_rpow_isLittleO_exp_neg (div_pos hb hd) hp)).const_mul_atTop hd
    refine tendsto_atBot_mono' _ ?_ (tendsto_neg_atTop_atBot.comp h)
    filter_upwards [eventually_ge_atTop 0] with t ht
    have hdt : -(d * (-t - -(b / d) * t ^ p)) = d * t - b * t ^ p := by
      field_simp
      ring
    rw [Function.comp_apply, hdt]
    nlinarith [mul_le_mul_of_nonneg_right (le_max_right 1 (z.re + 1)) ht]
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
