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
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Moments.ComplexMGF
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Laplace-type integrals with superlinear power decay

For real `p > 1`, complex `s` with `-1 < s.re` and `b` with `0 < b.re`, and every complex `z`,
the kernel `t ↦ (t : ℂ) ^ s * Complex.exp (z * t - b * (t : ℂ) ^ (p : ℂ))` is Bochner integrable
on `(0, ∞)` (see `TauCeti.norm_cpow_mul_cexp_mul_sub_mul_cpow` and
`TauCeti.integrableOn_cpow_mul_cexp_mul_sub_mul_cpow_Ioi` in
`TauCeti.MeasureTheory.Integral.Exp.Decay`). Expanding `exp (z * t)` as its power series and
integrating term by term by dominated convergence evaluates the integral as the everywhere
convergent Gamma-coefficient series

`∑' n, z ^ n / n! * (b ^ (-(s + n + 1) / p) * (1 / p) * Γ ((s + n + 1) / p))`.

For real `q > -1` and `b > 0`, differentiating under the integral sign shows that the integral
`∫₀^∞ t ^ q exp (z t - b t ^ p) dt` is an entire function of `z` whose derivative is the moment of
order `q + 1`. For every real `q` and `b > 0` the kernel tends to zero at infinity, and for
`p > 0`, `0 < b.re`, `-1 < s.re` at `z = 0` the integral is a Gamma value,
`∫₀^∞ t ^ s exp (-b t ^ p) dt = b ^ (-(s + 1) / p) * (1 / p) * Γ ((s + 1) / p)`.

With `p = 3`, integrals of this shape represent the Scorer function `Hi`, which is `π⁻¹` times
the integral with `b = 1/3` and `s = 0`, and the sum of squares `Ai(z)² + Bi(z)²` of the Airy
functions, which is `π ^ (-3 / 2)` times the integral with `b = 1/12` and `s = -1/2`.

## Main results

* `TauCeti.hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_rpow`: the derivative in `z` of the
  integral is the integral of the kernel with `q` replaced by `q + 1`.
* `TauCeti.tendsto_cpow_mul_cexp_mul_sub_mul_rpow_atTop`: the kernel tends to zero at infinity.
* `TauCeti.integral_cpow_mul_cexp_neg_mul_cpow_Ioi`: complex-exponent and complex-rate
  counterpart of Mathlib's `integral_rpow_mul_exp_neg_mul_rpow`.
* `TauCeti.hasSum_integral_cpow_mul_cexp_mul_sub_mul_cpow_Ioi`: the everywhere convergent
  Maclaurin series in `z` of the half-line superlinear exponential-power Laplace integral.

The norm, integrability and differentiation arguments are extracted and generalized from the
proofs for the integral of `Ai² + Bi²` in `TauCeti.Analysis.SpecialFunctions.Airy.Product.Integral`.
The derivative is Mathlib's `ProbabilityTheory.hasDerivAt_integral_pow_mul_exp` for the measure
with density `t ^ q exp (-b t ^ p)` on `(0, ∞)`.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped Nat Topology NNReal ENNReal

namespace TauCeti

/-- For real `p > 1`, `q > -1` and `b > 0`, the derivative of
`w ↦ ∫₀^∞ t ^ q exp (w t - b t ^ p) dt` at `z` is `∫₀^∞ t ^ (q + 1) exp (z t - b t ^ p) dt`. -/
theorem hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_rpow {p q b : ℝ} (hp : 1 < p)
    (hq : -1 < q) (hb : 0 < b) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q : ℂ) * cexp (w * t - ((b * t ^ p : ℝ) : ℂ)))
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((q : ℂ) + 1) * cexp (z * t - ((b * t ^ p : ℝ) : ℂ))) z := by
  -- The weight `t ^ q exp (-b t ^ p)` as a density on `(0, ∞)`; the kernel integrals are
  -- the exponential moments of the identity against it, so Mathlib's moment derivative applies.
  set ρ : ℝ → ℝ≥0 := fun t => Real.toNNReal (t ^ q * Real.exp (-(b * t ^ p)))
  have hρm : Measurable ρ := by fun_prop
  have hρt : ∀ t : ℝ, 0 < t → ((ρ t : ℝ≥0) : ℝ) = t ^ q * Real.exp (-(b * t ^ p)) :=
    fun t ht => Real.coe_toNNReal _ (by positivity)
  set μ := (volume.restrict (Ioi (0 : ℝ))).withDensity fun t => (ρ t : ℝ≥0∞)
  have hconv : ∀ (n : ℕ) (w : ℂ), ∫ t, (t : ℂ) ^ n * cexp (w * t) ∂μ =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((q : ℂ) + n) * cexp (w * t - ((b * t ^ p : ℝ) : ℂ)) := by
    intro n w
    rw [integral_withDensity_eq_integral_smul hρm]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [NNReal.smul_def, hρt t ht, real_smul, cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'),
      cpow_natCast]
    push_cast [← ofReal_cpow ht.le]
    rw [sub_eq_add_neg, Complex.exp_add]
    ring
  have hexp : ∀ s : ℝ, s ∈ ProbabilityTheory.integrableExpSet id μ := by
    intro s
    refine (integrable_withDensity_iff_integrable_smul hρm).2 ?_
    refine (integrableOn_rpow_mul_exp_mul_sub_mul_rpow hp hq hb s).congr_fun
      (fun t (ht : 0 < t) => ?_) measurableSet_Ioi
    rw [NNReal.smul_def, hρt t ht, smul_eq_mul, id, mul_assoc, ← Real.exp_add]
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
  have hb_eq : ((b * t ^ p : ℝ) : ℂ) = (b : ℂ) * (t : ℂ) ^ (p : ℂ) := by
    rw [ofReal_mul, ofReal_cpow ht.le]
  rw [Function.comp_apply, hb_eq, norm_cpow_mul_cexp_mul_sub_mul_cpow p b q z ht,
    ofReal_re, ofReal_re, mul_assoc, ← Real.exp_add]
  ring_nf

/-- For `0 < p`, `0 < b.re`, and `-1 < s.re`,
`∫ t in Ioi 0, (t : ℂ) ^ s * exp (-b * (t : ℂ) ^ (p : ℂ)) =
  b ^ (-(s + 1) / p) * (1 / p) * Γ ((s + 1) / p)`,
the complex-exponent and complex-rate counterpart of Mathlib's `integral_rpow_mul_exp_neg_mul_rpow`.
The proof follows Mathlib's `integral_rpow_mul_exp_neg_rpow` via the reciprocal-power
substitution `t = x ^ (1 / p)` and evaluates the resulting integral with
`Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos`. -/
theorem integral_cpow_mul_cexp_neg_mul_cpow_Ioi {p : ℝ} (hp : 0 < p) {b s : ℂ}
    (hb : 0 < b.re) (hs : -1 < s.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ s * cexp (-b * (t : ℂ) ^ (p : ℂ)) =
      b ^ (-(s + 1) / p) * (1 / (p : ℂ)) * Complex.Gamma ((s + 1) / p) := by
  have hp_ne : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hre : 0 < ((s + 1) / (p : ℂ)).re := by
    rw [Complex.div_ofReal_re, Complex.add_re, Complex.one_re]
    exact div_pos (by linarith) hp
  calc
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ s * cexp (-b * (t : ℂ) ^ (p : ℂ))
        = ∫ x in Ioi (0 : ℝ),
            ((1 / p) * x ^ (1 / p - 1)) •
              (((x ^ (1 / p) : ℝ) : ℂ) ^ s *
                cexp (-b * ((x ^ (1 / p) : ℝ) : ℂ) ^ (p : ℂ))) := by
          rw [← integral_comp_rpow_Ioi_of_pos (one_div_pos.mpr hp)]
    _ = ∫ x in Ioi (0 : ℝ),
          (1 / (p : ℂ)) * ((x : ℂ) ^ ((s + 1) / p - 1) * cexp (-(b * x))) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) => ?_
          have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
          have hpow : ((x ^ (1 / p) : ℝ) : ℂ) ^ s = (x : ℂ) ^ (((1 / p : ℝ) : ℂ) * s) :=
            (Complex.cpow_mul_ofReal_nonneg hx.le (1 / p) s).symm
          have hxp : ((x ^ (1 / p) : ℝ) : ℂ) ^ (p : ℂ) = (x : ℂ) := by
            rw [← Complex.ofReal_cpow (by positivity), ← Real.rpow_mul hx.le,
              one_div_mul_cancel hp.ne', Real.rpow_one]
          have hexp : ((1 / p - 1 : ℝ) : ℂ) + ((1 / p : ℝ) : ℂ) * s = (s + 1) / p - 1 := by
            push_cast
            field_simp
            ring
          rw [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
            Complex.ofReal_cpow hx.le, hpow, hxp, neg_mul]
          calc (1 / (p : ℂ) * (x : ℂ) ^ ((1 / p - 1 : ℝ) : ℂ)) *
                ((x : ℂ) ^ (((1 / p : ℝ) : ℂ) * s) * cexp (-(b * x)))
              = (1 / (p : ℂ)) * (((x : ℂ) ^ ((1 / p - 1 : ℝ) : ℂ) *
                  (x : ℂ) ^ (((1 / p : ℝ) : ℂ) * s)) * cexp (-(b * x))) := by ring
            _ = _ := by rw [← Complex.cpow_add _ _ hx0, hexp]
    _ = b ^ (-(s + 1) / p) * (1 / (p : ℂ)) * Complex.Gamma ((s + 1) / p) := by
          rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hre hb,
            neg_div]
          ring

/-- **Series expansion of a superlinear exponential-power Laplace integral.** For `1 < p`,
`0 < b.re`, `-1 < s.re`, and every `z : ℂ`,
`∫ t in Ioi 0, (t : ℂ) ^ s * exp (z * t - b * (t : ℂ) ^ (p : ℂ)) =
  ∑' n, z ^ n / n! * (b ^ (-(s + n + 1) / p) * (1 / p) * Γ ((s + n + 1) / p))`. -/
theorem hasSum_integral_cpow_mul_cexp_mul_sub_mul_cpow_Ioi {p : ℝ} (hp : 1 < p) {b s : ℂ}
    (hb : 0 < b.re) (hs : -1 < s.re) (z : ℂ) :
    HasSum
      (fun n : ℕ =>
        z ^ n / (n ! : ℂ) *
          (b ^ (-(s + n + 1) / p) * (1 / (p : ℂ)) * Complex.Gamma ((s + n + 1) / p)))
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ s * cexp (z * t - b * (t : ℂ) ^ (p : ℂ))) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  let F : ℕ → ℝ → ℂ := fun n t =>
    (z ^ n / (n ! : ℂ)) * ((t : ℂ) ^ (s + n) * cexp (-b * (t : ℂ) ^ (p : ℂ)))
  let bound : ℕ → ℝ → ℝ := fun n t =>
    (‖z‖ ^ n / (n ! : ℝ)) * (t ^ (s.re + n) * rexp (-b.re * t ^ p))
  have hbound_sum : ∀ t : ℝ, 0 < t →
      HasSum (fun n => bound n t) (t ^ s.re * rexp (‖z‖ * t - b.re * t ^ p)) := fun t ht => by
    have hexp := Real.exp_eq_exp_ℝ ▸ NormedSpace.expSeries_div_hasSum_exp (‖z‖ * t)
    convert hexp.mul_right (t ^ s.re * rexp (-b.re * t ^ p)) using 1
    · ext n
      simp only [bound]
      rw [mul_pow, Real.rpow_add ht, Real.rpow_natCast]
      ring
    · rw [← mul_assoc, mul_comm (rexp (‖z‖ * t)), mul_assoc, ← Real.exp_add, sub_eq_add_neg,
        neg_mul]
  have hdom : HasSum (fun n => ∫ t in Ioi (0 : ℝ), F n t)
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ s * cexp (z * t - b * (t : ℂ) ^ (p : ℂ))) := by
    refine hasSum_integral_of_dominated_convergence bound
      (fun n => Measurable.aestronglyMeasurable (by fun_prop))
      (fun n => ?_) ?_ ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      have hnorm := norm_cpow_mul_cexp_mul_sub_mul_cpow p b (s + n) 0 ht
      simp only [zero_mul, zero_sub, zero_re, add_re, natCast_re, ← neg_mul] at hnorm
      dsimp only [F, bound]
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, hnorm]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      exact (hbound_sum t ht).summable
    · refine (integrableOn_rpow_mul_exp_mul_sub_mul_rpow hp hs hb ‖z‖).congr_fun
        (fun t (ht : 0 < t) => (hbound_sum t ht).tsum_eq.symm) measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      have hexp := Complex.exp_eq_exp_ℂ ▸ NormedSpace.expSeries_div_hasSum_exp (z * (t : ℂ))
      convert hexp.mul_right ((t : ℂ) ^ s * cexp (-b * (t : ℂ) ^ (p : ℂ))) using 1
      · ext n
        simp only [F]
        rw [mul_pow, Complex.cpow_add _ _ ht0, Complex.cpow_natCast]
        ring
      · rw [← mul_assoc, mul_comm (cexp (z * t)), mul_assoc, ← Complex.exp_add, sub_eq_add_neg,
          neg_mul]
  refine hdom.congr_fun fun n => ?_
  have hsn : -1 < (s + n).re := by
    rw [Complex.add_re, Complex.natCast_re]
    linarith [n.cast_nonneg (α := ℝ)]
  simp only [F]
  rw [integral_const_mul, integral_cpow_mul_cexp_neg_mul_cpow_Ioi hp0 hb hsn]

end TauCeti
