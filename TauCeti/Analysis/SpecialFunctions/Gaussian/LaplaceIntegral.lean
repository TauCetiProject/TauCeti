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
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic

/-!
# Half-line Gaussian–Laplace integrals

This file develops integrability, positive scaling, differentiation with respect to the Laplace
parameter, and Mellin-parameter holomorphy for half-line integrals of the form

  `∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)`

with complex quadratic rate `b : ℂ` (`0 < b.re`), Mellin exponent `s : ℂ`, and linear Laplace
parameter `z : ℂ`, alongside real majorants for `b ≥ 0`. Completing the square on
`-b.re u² - z.re u` absorbs the linear term into half the Gaussian weight, so the integral
converges on `(0, ∞)` whenever `0 < b.re` and `0 < s.re` for every `z : ℂ`, defines an entire
function of `z` whose derivative shifts `s - 1` to `s` with a minus sign, and defines a holomorphic
function of `s` on the open right half-plane `{s : ℂ | 0 < s.re}`.

At `b = 1 / 2` and `s = a + 1 / 2`, this integral is the half-line Laplace kernel of Weber's
parabolic cylinder function `U(a, z)` (DLMF 12.5.1), providing both its differential-equation
derivative shifts and the termwise shifted integrals of the Laplace–Hermite rotational series.

## Main results

* `TauCeti.integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi`: `u ↦ u ^ s * exp (-b u² - c u)` is
  integrable on `(0, ∞)` for `0 < b` and `-1 < s`.
* `TauCeti.integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_pos`,
  `TauCeti.integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_nonneg`: tail integrability on
  `(a, ∞)` (`0 < a`) for `0 < b` with arbitrary `(s, c)` and for `0 ≤ b` when `0 < c` or
  `0 ≤ c ∧ s < -1`.
* `TauCeti.norm_cpow_mul_cexp_neg_mul_sq_sub_mul`: pointwise norm formula on `(0, ∞)` for
  `(u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)`.
* `TauCeti.integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi`,
  `TauCeti.integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_of_pos`: complex integrability on
  `(0, ∞)` for `0 < b.re` and `0 < s.re`, and on `(a, ∞)` (`0 < a`) for `0 < b.re` and any `s`.
* `TauCeti.integral_cpow_mul_cexp_neg_mul_sq_mul_sq_sub_mul_Ioi_eq_cpow_mul_integral`: positive
  scaling `v = c u` (`0 < c`) pulls out `(c : ℂ) ^ (-s)` and replaces `(b c², z)` by `(b, z / c)`.
* `TauCeti.hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi`,
  `TauCeti.differentiable_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi`: derivative in `z : ℂ`
  and entireness on `ℂ` for `0 < b.re` and `0 < s.re`.
* `TauCeti.differentiableOn_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi`: holomorphy in `s` on
  `{s : ℂ | 0 < s.re}` for `0 < b.re` and any `z : ℂ`.

## References

* *NIST Digital Library of Mathematical Functions*, [§12.5(i)](https://dlmf.nist.gov/12.5.i).
-/

public section

open Complex Filter MeasureTheory Real Set
open scoped Topology

namespace TauCeti

/-- On `(0, ∞)`, `u ↦ u ^ s * exp (-b u² - c u)` is integrable whenever `0 < b` and `-1 < s`. -/
theorem integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi {b s : ℝ} (hb : 0 < b) (hs : -1 < s)
    (c : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ s * rexp (-b * u ^ 2 - c * u)) (Ioi 0) := by
  have hmaj : IntegrableOn
      (fun u : ℝ => rexp (c ^ 2 / (2 * b)) * (u ^ s * rexp (-(b / 2) * u ^ 2))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq (half_pos hb) hs).const_mul _
  refine hmaj.mono'
    (by fun_prop : Measurable fun u : ℝ => u ^ s * rexp (-b * u ^ 2 - c * u)).aestronglyMeasurable
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
  rw [Real.norm_of_nonneg (by positivity)]
  calc u ^ s * rexp (-b * u ^ 2 - c * u)
      ≤ u ^ s * (rexp (c ^ 2 / (2 * b)) * rexp (-(b / 2) * u ^ 2)) :=
        mul_le_mul_of_nonneg_left (exp_neg_mul_sq_sub_mul_le hb c u) (by positivity)
    _ = rexp (c ^ 2 / (2 * b)) * (u ^ s * rexp (-(b / 2) * u ^ 2)) := by ring

private theorem rpow_le_rpow_sub_mul_rpow_max {a u : ℝ} (ha : 0 < a) (hu : a < u) (s : ℝ) :
    u ^ s ≤ a ^ (s - max s 0) * u ^ max s 0 := by
  set m := max s 0
  have hu0 : 0 < u := ha.trans hu
  have hua : 1 ≤ u / a := (one_le_div ha).mpr hu.le
  have hle : (u / a) ^ s ≤ (u / a) ^ m :=
    Real.rpow_le_rpow_of_exponent_le hua (le_max_left s 0)
  rw [Real.div_rpow hu0.le ha.le, Real.div_rpow hu0.le ha.le,
    div_le_div_iff₀ (Real.rpow_pos_of_pos ha s) (Real.rpow_pos_of_pos ha m)] at hle
  rw [Real.rpow_sub ha, div_mul_eq_mul_div, le_div_iff₀ (Real.rpow_pos_of_pos ha m)]
  linarith

/-- For `0 < a` and `0 < b`, `u ↦ u ^ s * exp (-b u² - c u)` is integrable on `(a, ∞)` for every
real exponent `s` and linear parameter `c`. -/
theorem integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_pos {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (s c : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ s * rexp (-b * u ^ 2 - c * u)) (Ioi a) := by
  set m := max s 0
  have hm : -1 < m := lt_of_lt_of_le neg_one_lt_zero (le_max_right s 0)
  have hmaj : IntegrableOn
      (fun u : ℝ => a ^ (s - m) * (u ^ m * rexp (-b * u ^ 2 - c * u))) (Ioi a) :=
    ((integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi hb hm c).mono_set
      (Ioi_subset_Ioi ha.le)).const_mul _
  refine hmaj.mono'
    (by fun_prop : Measurable fun u : ℝ => u ^ s * rexp (-b * u ^ 2 - c * u)).aestronglyMeasurable
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : a < u)
  have hu0 : 0 < u := ha.trans hu
  rw [Real.norm_of_nonneg (by positivity)]
  calc u ^ s * rexp (-b * u ^ 2 - c * u)
      ≤ (a ^ (s - m) * u ^ m) * rexp (-b * u ^ 2 - c * u) :=
        mul_le_mul_of_nonneg_right (rpow_le_rpow_sub_mul_rpow_max ha hu s) (Real.exp_pos _).le
    _ = a ^ (s - m) * (u ^ m * rexp (-b * u ^ 2 - c * u)) := by ring

/-- For `0 < a` and `0 ≤ b`, `u ↦ u ^ s * exp (-b u² - c u)` is integrable on `(a, ∞)` whenever
`0 < c`, or `0 ≤ c` and `s < -1`. -/
theorem integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_nonneg {a b s c : ℝ} (ha : 0 < a)
    (hb : 0 ≤ b) (hc : 0 < c ∨ (0 ≤ c ∧ s < -1)) :
    IntegrableOn (fun u : ℝ => u ^ s * rexp (-b * u ^ 2 - c * u)) (Ioi a) := by
  have hmeas : AEStronglyMeasurable (fun u : ℝ => u ^ s * rexp (-b * u ^ 2 - c * u))
      (volume.restrict (Ioi a)) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  rcases hc with hc | ⟨hc, hs⟩
  · set m := max s 0
    have hm : -1 < m := lt_of_lt_of_le neg_one_lt_zero (le_max_right s 0)
    have hmaj : IntegrableOn
        (fun u : ℝ => a ^ (s - m) * (u ^ m * rexp (-c * u ^ (1 : ℝ)))) (Ioi a) :=
      ((integrableOn_rpow_mul_exp_neg_mul_rpow hm zero_lt_one hc).mono_set
        (Ioi_subset_Ioi ha.le)).const_mul _
    refine hmaj.mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : a < u)
    have hu0 : 0 < u := ha.trans hu
    rw [Real.norm_of_nonneg (by positivity), Real.rpow_one]
    calc u ^ s * rexp (-b * u ^ 2 - c * u)
        ≤ (a ^ (s - m) * u ^ m) * rexp (-c * u) :=
          mul_le_mul (rpow_le_rpow_sub_mul_rpow_max ha hu s)
            (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])) (Real.exp_pos _).le (by positivity)
      _ = a ^ (s - m) * (u ^ m * rexp (-c * u)) := by ring
  · refine (integrableOn_Ioi_rpow_of_lt hs ha).mono' hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : a < u)
    have hu0 : 0 < u := ha.trans hu
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u]))

private theorem re_neg_mul_sq_sub_mul (b z : ℂ) (u : ℝ) :
    (-b * (u : ℂ) ^ 2 - z * u).re = -b.re * u ^ 2 - z.re * u := by
  simp [sq]

/-- For `0 < u` and any `b s z : ℂ`, the norm of
`(u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)` is
`u ^ (s.re - 1) * exp (-b.re * u ^ 2 - z.re * u)`. -/
theorem norm_cpow_mul_cexp_neg_mul_sq_sub_mul (b s z : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)‖ =
      u ^ (s.re - 1) * rexp (-b.re * u ^ 2 - z.re * u) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp,
    re_neg_mul_sq_sub_mul]
  simp

/-- For `0 < b.re` and `0 < s.re`, the complex Gaussian–Laplace integrand
`u ↦ (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)` is integrable on `(0, ∞)` for every
`z : ℂ`. -/
theorem integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi {b s : ℂ} (hb : 0 < b.re)
    (hs : 0 < s.re) (z : ℂ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u))
      (Ioi 0) := by
  have hmaj := integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi hb (s := s.re - 1) (by linarith)
    z.re
  refine hmaj.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
  rw [norm_cpow_mul_cexp_neg_mul_sq_sub_mul b s z hu]

/-- For `0 < a` and `0 < b.re`, `u ↦ (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)` is
integrable on `(a, ∞)` for every `s z : ℂ`. -/
theorem integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_of_pos {a : ℝ} {b : ℂ} (ha : 0 < a)
    (hb : 0 < b.re) (s z : ℂ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u))
      (Ioi a) := by
  have hmaj := integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_pos ha hb (s.re - 1) z.re
  refine hmaj.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : a < u)
  rw [norm_cpow_mul_cexp_neg_mul_sq_sub_mul b s z (ha.trans hu)]

/-- Positive rescaling `v = c * u` (`0 < c`) in the half-line Gaussian–Laplace integral: for every
`b s z : ℂ`, `∫_{u > 0} u^{s - 1} exp (-(b c²) u² - z u) du` equals
`c^{-s} ∫_{v > 0} v^{s - 1} exp (-b v² - (z / c) v) dv`. -/
theorem integral_cpow_mul_cexp_neg_mul_sq_mul_sq_sub_mul_Ioi_eq_cpow_mul_integral {c : ℝ}
    (hc : 0 < c) (b s z : ℂ) :
    (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (s - 1) * cexp (-(b * (c : ℂ) ^ 2) * (u : ℂ) ^ 2 - z * u)) =
      (c : ℂ) ^ (-s) * ∫ v in Ioi (0 : ℝ),
        (v : ℂ) ^ (s - 1) * cexp (-b * (v : ℂ) ^ 2 - (z / c) * v) := by
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hm := mellin_comp_mul_left
    (fun v : ℝ => cexp (-b * (v : ℂ) ^ 2 - (z / c) * v)) s hc
  simp only [mellin, smul_eq_mul] at hm
  rw [← hm]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  congr 2
  push_cast
  field_simp

/-- For `0 < b.re` and `0 < s.re`, the Gaussian–Laplace integral
`w ↦ ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - w * u)` has complex
derivative `-∫ u in Ioi (0 : ℝ), (u : ℂ) ^ s * cexp (-b * (u : ℂ) ^ 2 - z * u)` at every `z : ℂ`. -/
theorem hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi {b s : ℂ} (hb : 0 < b.re)
    (hs : 0 < s.re) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - w * u))
      (-∫ u in Ioi (0 : ℝ), (u : ℂ) ^ s * cexp (-b * (u : ℂ) ^ 2 - z * u)) z := by
  have hball : Metric.ball z 1 ∈ 𝓝 z := Metric.ball_mem_nhds z zero_lt_one
  have hb_int : IntegrableOn
      (fun u : ℝ => u ^ s.re * rexp (-b.re * u ^ 2 - (-(|z.re| + 1)) * u)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi hb (by linarith) (-(|z.re| + 1))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun w (u : ℝ) => (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - w * u))
    (F' := fun w (u : ℝ) => -((u : ℂ) ^ s * cexp (-b * (u : ℂ) ^ 2 - w * u)))
    (bound := fun u : ℝ => u ^ s.re * rexp (-b.re * u ^ 2 - (-(|z.re| + 1)) * u))
    hball
    (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi hb hs z)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hb_int ?_
  · simpa only [integral_neg] using h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u) w hw
    have hw_re : -(|z.re| + 1) ≤ w.re := by
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have h1 : |w.re - z.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm (w - z)) hw
      linarith [abs_lt.mp h1, le_abs_self z.re, neg_le_abs z.re]
    rw [norm_neg, show (u : ℂ) ^ s = (u : ℂ) ^ ((s + 1) - 1) by rw [add_sub_cancel_right],
      norm_cpow_mul_cexp_neg_mul_sq_sub_mul b (s + 1) w hu]
    simp only [Complex.add_re, Complex.one_re, add_sub_cancel_right]
    gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u) w _
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hid : HasDerivAt (fun ξ : ℂ => ξ * (u : ℂ)) (u : ℂ) w := by
      simpa using (hasDerivAt_id w).mul_const (u : ℂ)
    have hexp : HasDerivAt (fun ξ : ℂ => -b * (u : ℂ) ^ 2 - ξ * u) (-(u : ℂ)) w :=
      hid.const_sub (-b * (u : ℂ) ^ 2)
    have hcpow : (u : ℂ) ^ s = (u : ℂ) ^ (s - 1) * (u : ℂ) :=
      calc (u : ℂ) ^ s = (u : ℂ) ^ ((s - 1) + 1) := by rw [sub_add_cancel]
        _ = (u : ℂ) ^ (s - 1) * (u : ℂ) ^ (1 : ℂ) := Complex.cpow_add _ _ hu0
        _ = (u : ℂ) ^ (s - 1) * (u : ℂ) := by rw [Complex.cpow_one]
    convert hexp.cexp.const_mul ((u : ℂ) ^ (s - 1)) using 1
    rw [hcpow]
    ring

/-- For `0 < b.re` and `0 < s.re`, the Gaussian–Laplace integral
`z ↦ ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)` is an entire
function on `ℂ`. -/
theorem differentiable_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi {b s : ℂ} (hb : 0 < b.re)
    (hs : 0 < s.re) :
    Differentiable ℂ fun z : ℂ =>
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u) :=
  fun z => (hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi hb hs z).differentiableAt

/-- For `0 < b.re` and any `z : ℂ`, the Mellin parameter map
`s ↦ ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)` is holomorphic
on the open right half-plane `{s : ℂ | 0 < s.re}`. -/
theorem differentiableOn_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi {b : ℂ} (hb : 0 < b.re)
    (z : ℂ) :
    DifferentiableOn ℂ
      (fun s : ℂ =>
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u))
      {s : ℂ | 0 < s.re} := by
  let f : ℝ → ℂ := fun u => cexp (-b * (u : ℂ) ^ 2 - z * u)
  have hf_loc : LocallyIntegrableOn f (Ioi 0) :=
    (by fun_prop : Continuous f).continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hf_top : f =O[atTop] fun u : ℝ => rexp (-(b.re / 2) * u) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨rexp (z.re ^ 2 / (2 * b.re)), ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with u (hu : 1 ≤ u)
    have hu_sq : u ≤ u ^ 2 := by nlinarith
    rw [Complex.norm_exp, Real.norm_of_nonneg (Real.exp_pos _).le, re_neg_mul_sq_sub_mul]
    refine (exp_neg_mul_sq_sub_mul_le hb z.re u).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le
  have hf_bot : f =O[𝓝[>] 0] fun u : ℝ => u ^ (-(0 : ℝ)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨rexp (z.re ^ 2 / (2 * b.re)), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u (_ : 0 < u)
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one, Complex.norm_exp, re_neg_mul_sq_sub_mul]
    calc rexp (-b.re * u ^ 2 - z.re * u)
        ≤ rexp (z.re ^ 2 / (2 * b.re)) * rexp (-(b.re / 2) * u ^ 2) :=
          exp_neg_mul_sq_sub_mul_le hb z.re u
      _ ≤ rexp (z.re ^ 2 / (2 * b.re)) * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
      _ = rexp (z.re ^ 2 / (2 * b.re)) := mul_one _
  have hm : (fun s : ℂ =>
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)) =
      mellin f := by
    ext s
    simp [mellin, f]
  rw [hm]
  intro s hs
  exact (mellin_differentiableAt_of_isBigO_rpow_exp (half_pos hb) hf_loc hf_top hf_bot
    hs).differentiableWithinAt

end TauCeti
