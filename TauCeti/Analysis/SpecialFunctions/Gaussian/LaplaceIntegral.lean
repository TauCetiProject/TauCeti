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

/-!
# Half-line Gaussian–Laplace integrals

This file develops integrability, positive scaling, and complex differentiability for half-line
integrals of the form

  `∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)`

with quadratic rate `b > 0`, Mellin exponent `s : ℂ`, and linear Laplace parameter `z : ℂ`.
Completing the square absorbs the linear term into half the Gaussian weight, so the integral
converges whenever `0 < s.re` for every `z : ℂ`, defines an entire function of `z`, and defines a
holomorphic function of `s` on the open right half-plane `{s : ℂ | 0 < s.re}`.

## Main results

* `TauCeti.exp_neg_mul_sq_sub_mul_le`: completing the square bounds `exp (-b u² - c u)` by
  `exp (c² / (2 b)) * exp (-(b / 2) u²)` for `0 < b`.
* `TauCeti.integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi`: `u ↦ u ^ s * exp (-b u² - c u)` is
  integrable on `(0, ∞)` for `0 < b` and `-1 < s`, and
  `TauCeti.integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_pos` removes the lower bound on `s`
  on `(a, ∞)` for `0 < a`.
* `TauCeti.integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi`: complex integrability on `(0, ∞)`
  for `0 < b` and `0 < s.re`.
* `TauCeti.integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi`: positive scaling `v = c u` (`0 < c`)
  pulls out `(c : ℂ) ^ (-s)` and replaces `(b c², z)` by `(b, z / c)`.
* `TauCeti.differentiable_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi`: entireness in `z : ℂ` for
  `0 < b` and `0 < s.re`.
* `TauCeti.differentiableOn_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi`: holomorphy in `s` on
  `{s : ℂ | 0 < s.re}` for `0 < b` and any `z : ℂ`.

## References

* *NIST Digital Library of Mathematical Functions*, [§12.5(i)](https://dlmf.nist.gov/12.5.i).
-/

public section

open Complex Filter MeasureTheory Real Set
open scoped Topology

namespace TauCeti

/-- Completing the square bounds `exp (-b u² - c u)` uniformly in `u` by half the Gaussian weight
with prefactor `exp (c² / (2 b))`. -/
theorem exp_neg_mul_sq_sub_mul_le {b : ℝ} (hb : 0 < b) (c u : ℝ) :
    rexp (-b * u ^ 2 - c * u) ≤ rexp (c ^ 2 / (2 * b)) * rexp (-(b / 2) * u ^ 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hsq : 0 ≤ b / 2 * (u + c / b) ^ 2 := by positivity
  have hexpand : b / 2 * (u + c / b) ^ 2 = b / 2 * u ^ 2 + c * u + c ^ 2 / (2 * b) := by
    field_simp
    ring
  linarith

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

/-- Away from the origin (`0 < a`), `u ↦ u ^ s * exp (-b u² - c u)` is integrable on `(a, ∞)` for
every real exponent `s` and linear parameter `c` once `0 < b`. -/
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
  have hua : 1 ≤ u / a := (one_le_div ha).mpr hu.le
  have hrpow : u ^ s ≤ a ^ (s - m) * u ^ m := by
    have hle : (u / a) ^ s ≤ (u / a) ^ m :=
      Real.rpow_le_rpow_of_exponent_le hua (le_max_left s 0)
    rw [Real.div_rpow hu0.le ha.le, Real.div_rpow hu0.le ha.le,
      div_le_div_iff₀ (Real.rpow_pos_of_pos ha s) (Real.rpow_pos_of_pos ha m)] at hle
    rw [Real.rpow_sub ha, div_mul_eq_mul_div, le_div_iff₀ (Real.rpow_pos_of_pos ha m)]
    linarith
  rw [Real.norm_of_nonneg (by positivity)]
  calc u ^ s * rexp (-b * u ^ 2 - c * u)
      ≤ (a ^ (s - m) * u ^ m) * rexp (-b * u ^ 2 - c * u) :=
        mul_le_mul_of_nonneg_right hrpow (Real.exp_pos _).le
    _ = a ^ (s - m) * (u ^ m * rexp (-b * u ^ 2 - c * u)) := by ring

private theorem re_neg_mul_sq_sub_mul (b u : ℝ) (z : ℂ) :
    (-(b : ℂ) * (u : ℂ) ^ 2 - z * u).re = -b * u ^ 2 - z.re * u := by
  simp [sq]

/-- Pointwise norm of `(u : ℂ) ^ (s - 1) * cexp (-(b : ℂ) * (u : ℂ) ^ 2 - z * u)` for `0 < u`. -/
private theorem norm_cpow_mul_cexp_neg_mul_sq_sub_mul (b : ℝ) (s z : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ (s - 1) * cexp (-(b : ℂ) * (u : ℂ) ^ 2 - z * u)‖ =
      u ^ (s.re - 1) * rexp (-b * u ^ 2 - z.re * u) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp,
    re_neg_mul_sq_sub_mul]
  simp

/-- For `0 < b` and `0 < s.re`, the complex Gaussian–Laplace integrand
`u ↦ (u : ℂ) ^ (s - 1) * cexp (-(b : ℂ) * (u : ℂ) ^ 2 - z * u)` is integrable on `(0, ∞)` for every
`z : ℂ`. -/
theorem integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi {b : ℝ} {s : ℂ} (hb : 0 < b)
    (hs : 0 < s.re) (z : ℂ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * cexp (-(b : ℂ) * (u : ℂ) ^ 2 - z * u))
      (Ioi 0) := by
  have hmaj := integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi hb (s := s.re - 1) (by linarith)
    z.re
  refine hmaj.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
  rw [norm_cpow_mul_cexp_neg_mul_sq_sub_mul b s z hu]

/-- Positive rescaling `v = c * u` (`0 < c`) in the half-line Gaussian–Laplace integral:
`∫_{u > 0} u^{s - 1} exp (-(b c²) u² - z u) du` equals
`c^{-s} ∫_{v > 0} v^{s - 1} exp (-b v² - (z / c) v) dv`. -/
theorem integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi {c : ℝ} (hc : 0 < c) (b : ℝ) (s z : ℂ) :
    (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (s - 1) * cexp (-((b * c ^ 2 : ℝ) : ℂ) * (u : ℂ) ^ 2 - z * u)) =
      (c : ℂ) ^ (-s) * ∫ v in Ioi (0 : ℝ),
        (v : ℂ) ^ (s - 1) * cexp (-(b : ℂ) * (v : ℂ) ^ 2 - (z / c) * v) := by
  let g : ℝ → ℂ := fun v => (v : ℂ) ^ (s - 1) * cexp (-(b : ℂ) * (v : ℂ) ^ 2 - (z / c) * v)
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hpoint : EqOn
      (fun u : ℝ => (u : ℂ) ^ (s - 1) * cexp (-((b * c ^ 2 : ℝ) : ℂ) * (u : ℂ) ^ 2 - z * u))
      (fun u : ℝ => (c : ℂ) ^ (1 - s) * g (c * u)) (Ioi 0) := by
    intro u (hu : 0 < u)
    have hmul_cpow : ((c * u : ℝ) : ℂ) ^ (s - 1) = (c : ℂ) ^ (s - 1) * (u : ℂ) ^ (s - 1) := by
      rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le hu.le]
    have hpow_cancel : (c : ℂ) ^ (1 - s) * (c : ℂ) ^ (s - 1) = 1 := by
      rw [← Complex.cpow_add _ _ hc0, show (1 - s) + (s - 1) = 0 by ring, Complex.cpow_zero]
    have hexp_eq :
        -(b : ℂ) * ((c * u : ℝ) : ℂ) ^ 2 - (z / c) * ((c * u : ℝ) : ℂ) =
          -((b * c ^ 2 : ℝ) : ℂ) * (u : ℂ) ^ 2 - z * u := by
      push_cast
      field_simp
    dsimp only [g]
    rw [hmul_cpow, hexp_eq, ← mul_assoc, ← mul_assoc, hpow_cancel, one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul,
    integral_comp_mul_left_Ioi g 0 hc, mul_zero, Complex.real_smul, Complex.ofReal_inv]
  have hc_pow : (c : ℂ) ^ (1 - s) * (c : ℂ)⁻¹ = (c : ℂ) ^ (-s) := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hc0]
    congr 1
    ring
  rw [← mul_assoc, hc_pow]

/-- For `0 < b` and `0 < s.re`, the Gaussian–Laplace integral
`z ↦ ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-(b : ℂ) * (u : ℂ) ^ 2 - z * u)` is an entire
function on `ℂ`. -/
theorem differentiable_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi {b : ℝ} {s : ℂ} (hb : 0 < b)
    (hs : 0 < s.re) :
    Differentiable ℂ fun z : ℂ =>
      ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-(b : ℂ) * (u : ℂ) ^ 2 - z * u) := by
  intro z₀
  have hball : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ zero_lt_one
  have hb_int : IntegrableOn
      (fun u : ℝ => u ^ s.re * rexp (-b * u ^ 2 - (-(|z₀.re| + 1)) * u)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi hb (by linarith) (-(|z₀.re| + 1))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun z (u : ℝ) => (u : ℂ) ^ (s - 1) * cexp (-(b : ℂ) * (u : ℂ) ^ 2 - z * u))
    (F' := fun z (u : ℝ) => (u : ℂ) ^ (s - 1) * cexp (-(b : ℂ) * (u : ℂ) ^ 2 - z * u) * -(u : ℂ))
    (bound := fun u : ℝ => u ^ s.re * rexp (-b * u ^ 2 - (-(|z₀.re| + 1)) * u))
    hball
    (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi hb hs z₀)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hb_int ?_
  · exact h.2.differentiableAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u) z hz
    have hz_re : -(|z₀.re| + 1) ≤ z.re := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h1 : |z.re - z₀.re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm (z - z₀)) hz
      linarith [abs_lt.mp h1, le_abs_self z₀.re, neg_le_abs z₀.re]
    rw [norm_mul, norm_cpow_mul_cexp_neg_mul_sq_sub_mul b s z hu, norm_neg, Complex.norm_real,
      Real.norm_of_nonneg hu.le, mul_right_comm, ← Real.rpow_add_one hu.ne', sub_add_cancel]
    gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u _ z _
    have hid : HasDerivAt (fun w : ℂ => w * (u : ℂ)) (u : ℂ) z := by
      simpa using (hasDerivAt_id z).mul_const (u : ℂ)
    have hexp : HasDerivAt (fun w : ℂ => -(b : ℂ) * (u : ℂ) ^ 2 - w * u) (-(u : ℂ)) z :=
      hid.const_sub (-(b : ℂ) * (u : ℂ) ^ 2)
    simpa [mul_assoc] using hexp.cexp.const_mul ((u : ℂ) ^ (s - 1))

/-- For `0 < b` and any `z : ℂ`, the Mellin parameter map
`s ↦ ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-(b : ℂ) * (u : ℂ) ^ 2 - z * u)` is holomorphic
on the open right half-plane `{s : ℂ | 0 < s.re}`. -/
theorem differentiableOn_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi {b : ℝ} (hb : 0 < b)
    (z : ℂ) :
    DifferentiableOn ℂ
      (fun s : ℂ =>
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-(b : ℂ) * (u : ℂ) ^ 2 - z * u))
      {s : ℂ | 0 < s.re} := by
  let f : ℝ → ℂ := fun u => cexp (-(b : ℂ) * (u : ℂ) ^ 2 - z * u)
  have hf_loc : LocallyIntegrableOn f (Ioi 0) :=
    (by fun_prop : Continuous f).continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hf_top : f =O[atTop] fun u : ℝ => rexp (-(b / 2) * u) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨rexp (z.re ^ 2 / (2 * b)), ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with u (hu : 1 ≤ u)
    have hu_sq : u ≤ u ^ 2 := by nlinarith
    rw [Complex.norm_exp, Real.norm_of_nonneg (Real.exp_pos _).le, re_neg_mul_sq_sub_mul]
    refine (exp_neg_mul_sq_sub_mul_le hb z.re u).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le
  have hf_bot : f =O[𝓝[>] 0] fun u : ℝ => u ^ (-(0 : ℝ)) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨rexp (z.re ^ 2 / (2 * b)), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u (_ : 0 < u)
    rw [neg_zero, Real.rpow_zero, norm_one, mul_one, Complex.norm_exp, re_neg_mul_sq_sub_mul]
    calc rexp (-b * u ^ 2 - z.re * u)
        ≤ rexp (z.re ^ 2 / (2 * b)) * rexp (-(b / 2) * u ^ 2) :=
          exp_neg_mul_sq_sub_mul_le hb z.re u
      _ ≤ rexp (z.re ^ 2 / (2 * b)) * 1 := by
          gcongr
          exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg u])
      _ = rexp (z.re ^ 2 / (2 * b)) := mul_one _
  have hm : (fun s : ℂ =>
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-(b : ℂ) * (u : ℂ) ^ 2 - z * u)) =
      mellin f := by
    ext s
    simp [mellin, f]
  rw [hm]
  intro s hs
  exact (mellin_differentiableAt_of_isBigO_rpow_exp (half_pos hb) hf_loc hf_top hf_bot
    hs).differentiableWithinAt

end TauCeti
