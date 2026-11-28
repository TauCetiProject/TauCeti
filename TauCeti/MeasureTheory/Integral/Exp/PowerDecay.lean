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
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Laplace-type integrals with superlinear power decay

For real `p > 1`, complex `s` with `-1 < s.re` and `b` with `0 < b.re`, and every complex `z`,
the kernel `t ↦ (t : ℂ) ^ s * Complex.exp (z * t - b * (t : ℂ) ^ (p : ℂ))` is Bochner integrable
on `(0, ∞)` (see `Real.norm_cpow_mul_cexp_mul_sub_mul_cpow` and
`TauCeti.integrableOn_cpow_mul_cexp_mul_sub_mul_cpow_Ioi` in
`TauCeti.MeasureTheory.Integral.Exp.Decay`). Expanding `exp (z * t)` as its power series and
integrating term by term by dominated convergence evaluates the integral as the everywhere
convergent Gamma-coefficient series

`∑' n, z ^ n / n! * (b ^ (-(s + n + 1) / p) * (1 / p) * Γ ((s + n + 1) / p))`.

Differentiating under the integral sign shows that the integral
`∫₀^∞ t ^ s exp (z t - b t ^ p) dt` is an entire function of `z` whose derivative is the moment of
order `s + 1`. For `p > 1`, `0 < b.re`, and every `s, z : ℂ` the kernel tends to zero at infinity,
and for `p > 0`, `0 < b.re`, `-1 < s.re` at `z = 0` the integral is a Gamma value,
`∫₀^∞ t ^ s exp (-b t ^ p) dt = b ^ (-(s + 1) / p) * (1 / p) * Γ ((s + 1) / p)`.

With `p = 3`, integrals of this shape represent the Scorer function `Hi`, which is `π⁻¹` times
the integral with `b = 1/3` and `s = 0`, and the sum of squares `Ai(z)² + Bi(z)²` of the Airy
functions, which is `π ^ (-3 / 2)` times the integral with `b = 1/12` and `s = -1/2`.

## Main results

* `TauCeti.hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_cpow_Ioi`,
  `TauCeti.hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_pow_Ioi`: the derivative in `z` of the
  integral is the integral of the kernel with `s` replaced by `s + 1`.
* `TauCeti.tendsto_cpow_mul_cexp_mul_sub_mul_cpow_atTop`: the kernel tends to zero at infinity.
* `TauCeti.integral_cpow_mul_cexp_neg_mul_cpow_Ioi`: complex-exponent and complex-rate
  counterpart of Mathlib's `integral_rpow_mul_exp_neg_mul_rpow`.
* `TauCeti.hasSum_integral_cpow_mul_cexp_mul_sub_mul_cpow_Ioi`: the everywhere convergent
  Maclaurin series in `z` of the half-line superlinear exponential-power Laplace integral.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped Nat Topology

namespace TauCeti

/-- For `1 < p`, `0 < b.re`, and `-1 < s.re`, the derivative of
`w ↦ ∫₀^∞ (t : ℂ) ^ s * exp (w * t - b * (t : ℂ) ^ (p : ℂ)) dt` at `z` is
`∫₀^∞ (t : ℂ) ^ (s + 1) * exp (z * t - b * (t : ℂ) ^ (p : ℂ)) dt`. -/
theorem hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_cpow_Ioi {p : ℝ} (hp : 1 < p) {b s : ℂ}
    (hb : 0 < b.re) (hs : -1 < s.re) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ s * cexp (w * t - b * (t : ℂ) ^ (p : ℂ)))
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s + 1) * cexp (z * t - b * (t : ℂ) ^ (p : ℂ))) z := by
  have hs1 : -1 < s.re + 1 := by linarith
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun w (t : ℝ) => (t : ℂ) ^ s * cexp (w * t - b * (t : ℂ) ^ (p : ℂ)))
    (F' := fun w (t : ℝ) => (t : ℂ) ^ (s + 1) * cexp (w * t - b * (t : ℂ) ^ (p : ℂ)))
    (bound := fun t : ℝ => t ^ (s.re + 1) * rexp ((z.re + 1) * t - b.re * t ^ p))
    (Metric.ball_mem_nhds z zero_lt_one)
    (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (integrableOn_cpow_mul_cexp_mul_sub_mul_cpow_Ioi hp hb hs z)
    (Measurable.aestronglyMeasurable (by fun_prop))
    ?_
    (integrableOn_rpow_mul_exp_mul_sub_mul_rpow hp hs1 hb (z.re + 1))
    ?_
  · exact h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
    have hw_re : w.re < z.re + 1 := by
      have hre : (w - z).re < 1 :=
        (Complex.re_le_norm (w - z)).trans_lt (mem_ball_iff_norm.mp hw)
      rw [Complex.sub_re] at hre
      linarith
    rw [Real.norm_cpow_mul_cexp_mul_sub_mul_cpow p b (s + 1) w ht, Complex.add_re, Complex.one_re]
    gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w _
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hexp : HasDerivAt (fun ξ : ℂ => ξ * t - b * (t : ℂ) ^ (p : ℂ)) t w := by
      simpa using ((hasDerivAt_id w).mul_const (t : ℂ)).sub_const (b * (t : ℂ) ^ (p : ℂ))
    convert hexp.cexp.const_mul ((t : ℂ) ^ s) using 1
    rw [Complex.cpow_add _ _ ht0, Complex.cpow_one]
    ring

/-- Natural-power companion to `TauCeti.hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_cpow_Ioi`:
for `1 < n`, `0 < b.re`, and `-1 < s.re`, the derivative of
`w ↦ ∫₀^∞ (t : ℂ) ^ s * exp (w * t - b * (t : ℂ) ^ n) dt` at `z` is
`∫₀^∞ (t : ℂ) ^ (s + 1) * exp (z * t - b * (t : ℂ) ^ n) dt`. -/
theorem hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_pow_Ioi {n : ℕ} (hn : 1 < n) {b s : ℂ}
    (hb : 0 < b.re) (hs : -1 < s.re) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ s * cexp (w * t - b * (t : ℂ) ^ n))
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s + 1) * cexp (z * t - b * (t : ℂ) ^ n)) z := by
  simpa only [Complex.ofReal_natCast, Complex.cpow_natCast] using
    hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_cpow_Ioi (p := n) (by exact_mod_cast hn) hb hs z

/-- For `1 < p` and `0 < b.re`, every `s z : ℂ`, the kernel
`t ↦ (t : ℂ) ^ s * exp (z * t - b * (t : ℂ) ^ (p : ℂ))` tends to zero at infinity. -/
theorem tendsto_cpow_mul_cexp_mul_sub_mul_cpow_atTop {p : ℝ} (hp : 1 < p) {b : ℂ}
    (hb : 0 < b.re) (s z : ℂ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ s * cexp (z * t - b * (t : ℂ) ^ (p : ℂ))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  -- The exponent `(Re z + 1) t - Re b * t ^ p` tends to `-∞`: with `d = max 1 (Re z + 1)`, it is
  -- at most `d t - Re b * t ^ p = -d ((Re b / d) t ^ p - t)`, and `exp (-c t ^ p) = o(exp (-t))`.
  have hpoly : Tendsto (fun t : ℝ => (z.re + 1) * t - b.re * t ^ p) atTop atBot := by
    set d := max 1 (z.re + 1)
    have hd : 0 < d := lt_max_of_lt_left one_pos
    have h := (Real.isLittleO_exp_comp_exp_comp.1
      (exp_neg_mul_rpow_isLittleO_exp_neg (div_pos hb hd) hp)).const_mul_atTop hd
    refine tendsto_atBot_mono' _ ?_ (tendsto_neg_atTop_atBot.comp h)
    filter_upwards [eventually_ge_atTop 0] with t ht
    have hdt : -(d * (-t - -(b.re / d) * t ^ p)) = d * t - b.re * t ^ p := by
      field_simp
      ring
    rw [Function.comp_apply, hdt]
    nlinarith [mul_le_mul_of_nonneg_right (le_max_right 1 (z.re + 1)) ht]
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s.re 1 one_pos).mul
    (Real.tendsto_exp_atBot.comp hpoly)
  rw [zero_mul] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [Function.comp_apply, Real.norm_cpow_mul_cexp_mul_sub_mul_cpow p b s z ht, mul_assoc,
    ← Real.exp_add]
  ring_nf

/-- For `0 < p`, `0 < b.re`, and `-1 < s.re`,
`∫ t in Ioi 0, (t : ℂ) ^ s * exp (-b * (t : ℂ) ^ (p : ℂ)) =
  b ^ (-(s + 1) / p) * (1 / p) * Γ ((s + 1) / p)`,
the complex-exponent and complex-rate counterpart of Mathlib's
`integral_rpow_mul_exp_neg_mul_rpow`. -/
theorem integral_cpow_mul_cexp_neg_mul_cpow_Ioi {p : ℝ} (hp : 0 < p) {b s : ℂ}
    (hb : 0 < b.re) (hs : -1 < s.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ s * cexp (-b * (t : ℂ) ^ (p : ℂ)) =
      b ^ (-(s + 1) / p) * (1 / (p : ℂ)) * Complex.Gamma ((s + 1) / p) := by
  -- Follow Mathlib's `integral_rpow_mul_exp_neg_rpow` via the substitution `t = x ^ (1 / p)` and
  -- evaluate the resulting integral with `Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos`.
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
    have hexp := Real.exp_eq_exp_ℝ ▸
      hasSum_mul_pow_div_factorial_mul_exp ‖z‖ t (t ^ s.re) (-b.re * t ^ p)
    convert hexp using 1
    · ext n
      simp only [bound]
      rw [Real.rpow_add ht, Real.rpow_natCast]
    · rw [sub_eq_add_neg, neg_mul]
  have hdom : HasSum (fun n => ∫ t in Ioi (0 : ℝ), F n t)
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ s * cexp (z * t - b * (t : ℂ) ^ (p : ℂ))) := by
    refine hasSum_integral_of_dominated_convergence bound
      (fun n => Measurable.aestronglyMeasurable (by fun_prop))
      (fun n => ?_) ?_ ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      have hnorm := Real.norm_cpow_mul_cexp_mul_sub_mul_cpow p b (s + n) 0 ht
      simp only [zero_mul, zero_sub, zero_re, add_re, natCast_re, ← neg_mul] at hnorm
      dsimp only [F, bound]
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast, hnorm]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      exact (hbound_sum t ht).summable
    · refine (integrableOn_rpow_mul_exp_mul_sub_mul_rpow hp hs hb ‖z‖).congr_fun
        (fun t (ht : 0 < t) => (hbound_sum t ht).tsum_eq.symm) measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      have hexp := Complex.exp_eq_exp_ℂ ▸
        hasSum_mul_pow_div_factorial_mul_exp z (t : ℂ) ((t : ℂ) ^ s) (-b * (t : ℂ) ^ (p : ℂ))
      convert hexp using 1
      · ext n
        simp only [F]
        rw [Complex.cpow_add _ _ ht0, Complex.cpow_natCast]
      · rw [sub_eq_add_neg, neg_mul]
  refine hdom.congr_fun fun n => ?_
  have hsn : -1 < (s + n).re := by
    rw [Complex.add_re, Complex.natCast_re]
    linarith [n.cast_nonneg (α := ℝ)]
  simp only [F]
  rw [integral_const_mul, integral_cpow_mul_cexp_neg_mul_cpow_Ioi hp0 hb hsn]

end TauCeti
