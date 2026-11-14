/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.MellinTransform

/-!
# Mellin–Gaussian–Laplace integrals on the positive half-line

For `Re a > 0`, `Re b > 0`, and arbitrary `z : ℂ`, the half-line integral

  `∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t)`

converges absolutely: the quadratic decay `exp (-Re a · t²)` dominates the linear factor
`exp (-Re z · t)` at infinity regardless of the sign of `Re z`, while `Re b > 0` controls the power
singularity at the origin. At `a = 1 / 2`, this is the Laplace–Mellin integral kernel of Weber's
parabolic cylinder function `U(b - 1 / 2, z)` (DLMF 12.5.1).

This file establishes real and complex integrability, unconditional positive-real rescaling on
`(0, ∞)`, and complex differentiability under the integral sign with respect to both the linear
parameter `z` (on all of `ℂ`) and the exponent `b` (on `{b : ℂ | 0 < b.re}`).

## Main results

* `TauCeti.integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi`,
  `TauCeti.integrableOn_rpow_mul_exp_neg_sq_div_two_sub_mul_Ioi`: for `0 < a`, `-1 < s`, and
  `c : ℝ`, `t ↦ t ^ s * Real.exp (-a * t ^ 2 - c * t)` is integrable on `(0, ∞)`, together with
  its `a = 1 / 2` specialization.
* `TauCeti.norm_cpow_mul_cexp_neg_mul_sq_sub_mul`,
  `TauCeti.norm_cpow_mul_cexp_neg_sq_div_two_sub_mul`,
  `TauCeti.integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi`,
  `TauCeti.integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi`: pointwise norm on `(0, ∞)` and
  complex integrability for `0 < a.re`, `0 < b.re`, and all `z : ℂ`.
* `TauCeti.norm_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_le_add`,
  `TauCeti.norm_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_le_add`: uniform upper bound on a
  vertical strip `σ₁ ≤ b.re ≤ σ₂` (`0 < σ₁`) by the sum of the two real endpoint integrals.
* `TauCeti.integral_cpow_mul_cexp_neg_mul_mul_sq_sub_mul_Ioi_eq_cpow_neg_mul_integral`,
  `TauCeti.integral_cpow_mul_cexp_neg_mul_sq_div_two_sub_mul_Ioi_eq_cpow_neg_mul_integral`:
  positive-real scale change `v = c * u` (`0 < c`) on `(0, ∞)`, valid unconditionally for all
  complex parameters.
* `TauCeti.hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_right`,
  `TauCeti.hasDerivAt_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_right`,
  `TauCeti.differentiable_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_right`,
  `TauCeti.differentiable_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_right`: differentiation
  under the integral sign and entireness in `z : ℂ`.
* `TauCeti.hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_left`,
  `TauCeti.hasDerivAt_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_left`,
  `TauCeti.differentiableOn_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_left`,
  `TauCeti.differentiableOn_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_left`:
  differentiation under the integral sign and holomorphy in `b` on `{b : ℂ | 0 < b.re}`.

## References

* *NIST Digital Library of Mathematical Functions*, [§12.5](https://dlmf.nist.gov/12.5).
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace TauCeti

/-! ### Real and complex integrability and strip bounds -/

/-- For `0 < a`, `-1 < s`, and every `c : ℝ`, `t ↦ t ^ s * Real.exp (-a * t ^ 2 - c * t)` is
integrable on `(0, ∞)`. -/
theorem integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi {a s : ℝ} (ha : 0 < a) (hs : -1 < s)
    (c : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ s * Real.exp (-a * t ^ 2 - c * t)) (Ioi 0) := by
  -- Complete the square against half of the Gaussian weight.
  have hsq : IntegrableOn (fun t : ℝ => t ^ s * Real.exp (-(a / 2) * t ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq (half_pos ha) hs
  refine Integrable.mono' (hsq.const_mul (Real.exp (c ^ 2 / (2 * a))))
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  have hexp : -a * t ^ 2 - c * t ≤ c ^ 2 / (2 * a) + -(a / 2) * t ^ 2 := by
    have h0 : 0 ≤ a / 2 * (t + c / a) ^ 2 := by positivity
    have hid : a / 2 * (t + c / a) ^ 2 = a / 2 * t ^ 2 + c * t + c ^ 2 / (2 * a) := by
      field_simp
      ring
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_left_comm, ← Real.exp_add]
  gcongr

/-- At standard Gaussian normalization `a = 1 / 2`, `t ↦ t ^ s * Real.exp (-t ^ 2 / 2 - c * t)` is
integrable on `(0, ∞)` for `-1 < s` and every `c : ℝ`. -/
theorem integrableOn_rpow_mul_exp_neg_sq_div_two_sub_mul_Ioi {s : ℝ} (hs : -1 < s) (c : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ s * Real.exp (-t ^ 2 / 2 - c * t)) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi (a := 1 / 2) (by norm_num) hs c)
    |>.congr_fun (fun t _ => ?_) measurableSet_Ioi
  have hexp : -(1 / 2 : ℝ) * t ^ 2 - c * t = -t ^ 2 / 2 - c * t := by ring
  simp only [hexp]

/-- Pointwise norm of the complex Mellin–Gaussian–Laplace integrand for `0 < t`. -/
theorem norm_cpow_mul_cexp_neg_mul_sq_sub_mul (a b z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t)‖ =
      t ^ (b.re - 1) * Real.exp (-a.re * t ^ 2 - z.re * t) := by
  have hre : (-a * (t : ℂ) ^ 2 - z * t).re = -a.re * t ^ 2 - z.re * t := by
    simp [← Complex.ofReal_pow]
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re,
    Complex.norm_exp, hre]

/-- Pointwise norm of the `a = 1 / 2` complex Mellin–Gaussian–Laplace integrand for `0 < t`. -/
theorem norm_cpow_mul_cexp_neg_sq_div_two_sub_mul (b z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (b - 1) * Complex.exp (-(t : ℂ) ^ 2 / 2 - z * t)‖ =
      t ^ (b.re - 1) * Real.exp (-t ^ 2 / 2 - z.re * t) := by
  have h := norm_cpow_mul_cexp_neg_mul_sq_sub_mul (1 / 2) b z ht
  have hL : -(t : ℂ) ^ 2 / 2 - z * t = -(1 / 2 : ℂ) * (t : ℂ) ^ 2 - z * t := by ring
  have hR : -(1 / 2 : ℂ).re * t ^ 2 - z.re * t = -t ^ 2 / 2 - z.re * t := by norm_num; ring
  rw [hL, h, hR]

/-- For `0 < a.re`, `0 < b.re`, and every `z : ℂ`, the complex Mellin–Gaussian–Laplace integrand
`t ↦ (t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t)` is integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi {a b : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t))
      (Ioi 0) := by
  refine Integrable.mono'
    (integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi ha (by linarith : -1 < b.re - 1) z.re)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_cpow_mul_cexp_neg_mul_sq_sub_mul a b z ht]

/-- At standard Gaussian normalization `a = 1 / 2` (DLMF 12.5.1),
`t ↦ (t : ℂ) ^ (b - 1) * Complex.exp (-(t : ℂ) ^ 2 / 2 - z * t)` is integrable on `(0, ∞)` for
`0 < b.re` and every `z : ℂ`. -/
theorem integrableOn_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi {b : ℂ} (hb : 0 < b.re) (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (b - 1) * Complex.exp (-(t : ℂ) ^ 2 / 2 - z * t))
      (Ioi 0) := by
  have h := integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi (a := 1 / 2) (by norm_num) hb z
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  dsimp only
  congr 2
  ring

/-- On any vertical strip `σ₁ ≤ b.re ≤ σ₂` (`0 < σ₁`, `0 < a.re`), the norm of the complex
Mellin–Gaussian–Laplace integral is bounded by the sum of the two real integrals at `σ₁` and
`σ₂`. -/
theorem norm_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_le_add {a b : ℂ} {σ₁ σ₂ : ℝ}
    (ha : 0 < a.re) (hσ₁ : 0 < σ₁) (hlo : σ₁ ≤ b.re) (hhi : b.re ≤ σ₂) (z : ℂ) :
    ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t)‖ ≤
      (∫ t in Ioi (0 : ℝ), t ^ (σ₁ - 1) * Real.exp (-a.re * t ^ 2 - z.re * t)) +
        ∫ t in Ioi (0 : ℝ), t ^ (σ₂ - 1) * Real.exp (-a.re * t ^ 2 - z.re * t) := by
  have hint_b := integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi ha
    (by linarith : -1 < b.re - 1) z.re
  have hint_1 := integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi ha
    (by linarith : -1 < σ₁ - 1) z.re
  have hint_2 := integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi ha
    (by linarith : -1 < σ₂ - 1) z.re
  rw [← integral_add hint_1 hint_2]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) =>
    norm_cpow_mul_cexp_neg_mul_sq_sub_mul a b z ht]
  refine setIntegral_mono_on hint_b (hint_1.add hint_2) measurableSet_Ioi fun t (ht : 0 < t) => ?_
  simp only [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
  rcases le_total t 1 with ht1 | ht1
  · exact (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))
  · exact (Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))

/-- Vertical-strip norm bound at `a = 1 / 2`: for `0 < σ₁`, `σ₁ ≤ b.re`, and `b.re ≤ σ₂`,
`‖∫₀^∞ t^{b - 1} exp(-t² / 2 - z t) dt‖` is bounded by the sum of the real integrals at `σ₁` and
`σ₂`. -/
theorem norm_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_le_add {b : ℂ} {σ₁ σ₂ : ℝ}
    (hσ₁ : 0 < σ₁) (hlo : σ₁ ≤ b.re) (hhi : b.re ≤ σ₂) (z : ℂ) :
    ‖∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-(t : ℂ) ^ 2 / 2 - z * t)‖ ≤
      (∫ t in Ioi (0 : ℝ), t ^ (σ₁ - 1) * Real.exp (-t ^ 2 / 2 - z.re * t)) +
        ∫ t in Ioi (0 : ℝ), t ^ (σ₂ - 1) * Real.exp (-t ^ 2 / 2 - z.re * t) := by
  have h := norm_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_le_add (a := 1 / 2) (by norm_num)
    hσ₁ hlo hhi z
  have hL : (∫ t in Ioi (0 : ℝ),
      (t : ℂ) ^ (b - 1) * Complex.exp (-(t : ℂ) ^ 2 / 2 - z * t)) =
    ∫ t in Ioi (0 : ℝ),
      (t : ℂ) ^ (b - 1) * Complex.exp (-(1 / 2 : ℂ) * (t : ℂ) ^ 2 - z * t) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by congr 2; ring
  have hR : ∀ σ : ℝ, (∫ t in Ioi (0 : ℝ),
      t ^ (σ - 1) * Real.exp (-(1 / 2 : ℂ).re * t ^ 2 - z.re * t)) =
    ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * Real.exp (-t ^ 2 / 2 - z.re * t) :=
    fun _ => setIntegral_congr_fun measurableSet_Ioi fun t _ => by congr 2; norm_num; ring
  rwa [← hL, hR σ₁, hR σ₂] at h

/-! ### Positive-real rescaling on `(0, ∞)` -/

/-- Substituting `v = c * u` (`0 < c`) rescales the complex Mellin–Gaussian–Laplace integral on
`(0, ∞)` without any convergence assumption on `a`, `b`, or `z` (when non-integrable, both Bochner
integrals vanish). -/
theorem integral_cpow_mul_cexp_neg_mul_mul_sq_sub_mul_Ioi_eq_cpow_neg_mul_integral {c : ℝ}
    (hc : 0 < c) (a b z : ℂ) :
    (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (b - 1) * Complex.exp (-a * ((c : ℂ) * u) ^ 2 - z * u)) =
      (c : ℂ) ^ (-b) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (b - 1) * Complex.exp (-a * (v : ℂ) ^ 2 - (z / c) * v) := by
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have h := mellin_comp_mul_left
    (fun v : ℝ => Complex.exp (-a * (v : ℂ) ^ 2 - (z / c) * v)) b hc
  simp only [mellin, smul_eq_mul, Complex.ofReal_mul] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  congr 2
  field_simp

/-- Positive-real rescaling `v = c * u` (`0 < c`) for the `a = 1 / 2` Mellin–Gaussian–Laplace
integral on `(0, ∞)`. -/
theorem integral_cpow_mul_cexp_neg_mul_sq_div_two_sub_mul_Ioi_eq_cpow_neg_mul_integral {c : ℝ}
    (hc : 0 < c) (b z : ℂ) :
    (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (b - 1) * Complex.exp (-((c : ℂ) * u) ^ 2 / 2 - z * u)) =
      (c : ℂ) ^ (-b) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (b - 1) * Complex.exp (-(v : ℂ) ^ 2 / 2 - (z / c) * v) := by
  have h := integral_cpow_mul_cexp_neg_mul_mul_sq_sub_mul_Ioi_eq_cpow_neg_mul_integral hc
    (1 / 2) b z
  have hL : ∀ w : ℂ, -(1 / 2 : ℂ) * w ^ 2 = -w ^ 2 / 2 := fun _ => by ring
  simpa only [hL] using h

/-! ### Complex differentiability in the linear parameter `z` -/

private theorem neg_half_mul_sq_sub (z : ℂ) (t : ℝ) :
    -(1 / 2 : ℂ) * (t : ℂ) ^ 2 - z * t = -(t : ℂ) ^ 2 / 2 - z * t := by
  ring

/-- Differentiating the Mellin–Gaussian–Laplace integral with respect to `z` shifts `b` to `b + 1`
with a minus sign, for `0 < a.re`, `0 < b.re`, and every `z₀ : ℂ`. -/
theorem hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_right {a b : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (z₀ : ℂ) :
    HasDerivAt
      (fun z : ℂ =>
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t))
      (-(∫ t in Ioi (0 : ℝ), (t : ℂ) ^ b * Complex.exp (-a * (t : ℂ) ^ 2 - z₀ * t))) z₀ := by
  have hball : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ one_pos
  have hbint : Integrable (fun t : ℝ => t ^ b.re * Real.exp (-a.re * t ^ 2 - (z₀.re - 1) * t))
      (volume.restrict (Ioi 0)) :=
    integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi ha (by linarith : -1 < b.re) (z₀.re - 1)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun z (t : ℝ) => (t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t))
    (F' := fun z (t : ℝ) => -((t : ℂ) ^ b * Complex.exp (-a * (t : ℂ) ^ 2 - z * t)))
    (bound := fun t : ℝ => t ^ b.re * Real.exp (-a.re * t ^ 2 - (z₀.re - 1) * t))
    hball (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi ha hb z₀)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hbint ?_
  · simpa [integral_neg] using h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hre : z₀.re - 1 < z.re := by
      have h1 := Complex.abs_re_le_norm (z - z₀)
      rw [Complex.sub_re] at h1
      linarith [(abs_lt.mp (lt_of_le_of_lt h1 hz)).1]
    have hnorm := norm_cpow_mul_cexp_neg_mul_sq_sub_mul a (b + 1) z ht
    simp only [add_sub_cancel_right, Complex.add_re, Complex.one_re] at hnorm
    rw [norm_neg, hnorm]
    gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) z _
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hlin : HasDerivAt (fun w : ℂ => -a * (t : ℂ) ^ 2 - w * t) (-(t : ℂ)) z :=
      (((hasDerivAt_id z).mul_const (t : ℂ)).const_sub (-a * (t : ℂ) ^ 2)).congr_deriv (by ring)
    refine (hlin.cexp.const_mul ((t : ℂ) ^ (b - 1))).congr_deriv ?_
    have hpow : (t : ℂ) ^ (b - 1) * (t : ℂ) = (t : ℂ) ^ b :=
      calc (t : ℂ) ^ (b - 1) * (t : ℂ)
          = (t : ℂ) ^ (b - 1) * (t : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
        _ = (t : ℂ) ^ ((b - 1) + 1) := (Complex.cpow_add _ _ ht0).symm
        _ = (t : ℂ) ^ b := by congr 1; ring
    calc (t : ℂ) ^ (b - 1) * (Complex.exp (-a * (t : ℂ) ^ 2 - z * t) * -(t : ℂ))
        = -(((t : ℂ) ^ (b - 1) * (t : ℂ)) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t)) := by ring
      _ = -((t : ℂ) ^ b * Complex.exp (-a * (t : ℂ) ^ 2 - z * t)) := by rw [hpow]

/-- At `a = 1 / 2` (DLMF 12.5.1), differentiating
`z ↦ ∫ t in Ioi 0, (t : ℂ) ^ (b - 1) * exp (-t² / 2 - z t)` at `z₀` shifts `b` to `b + 1` with a
minus sign, for `0 < b.re` and every `z₀ : ℂ`. -/
theorem hasDerivAt_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_right {b : ℂ}
    (hb : 0 < b.re) (z₀ : ℂ) :
    HasDerivAt
      (fun z : ℂ =>
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-(t : ℂ) ^ 2 / 2 - z * t))
      (-(∫ t in Ioi (0 : ℝ), (t : ℂ) ^ b * Complex.exp (-(t : ℂ) ^ 2 / 2 - z₀ * t))) z₀ := by
  simpa only [neg_half_mul_sq_sub] using
    hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_right (a := 1 / 2) (by norm_num) hb z₀

/-- For `0 < a.re` and `0 < b.re`, the Mellin–Gaussian–Laplace integral is an entire function of
the linear parameter `z : ℂ`. -/
theorem differentiable_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_right {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) :
    Differentiable ℂ fun z : ℂ =>
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t) :=
  fun z => (hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_right ha hb z).differentiableAt

/-- For `0 < b.re`, `z ↦ ∫ t in Ioi 0, (t : ℂ) ^ (b - 1) * exp (-t² / 2 - z t)` is entire on
`ℂ`. -/
theorem differentiable_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_right {b : ℂ}
    (hb : 0 < b.re) :
    Differentiable ℂ fun z : ℂ =>
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-(t : ℂ) ^ 2 / 2 - z * t) := fun z =>
  (hasDerivAt_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_right hb z).differentiableAt

/-! ### Complex differentiability in the exponent `b` -/

/-- Differentiating the Mellin–Gaussian–Laplace integral with respect to `b` at `0 < b₀.re` inserts
a factor `Complex.log t` into the integrand, for `0 < a.re` and every `z : ℂ`. -/
theorem hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_left {a b₀ : ℂ} (ha : 0 < a.re)
    (hb₀ : 0 < b₀.re) (z : ℂ) :
    HasDerivAt
      (fun b : ℂ =>
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t))
      (∫ t in Ioi (0 : ℝ),
        Complex.log t * (t : ℂ) ^ (b₀ - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t)) b₀ := by
  let f : ℝ → ℂ := fun t => Complex.exp (-a * (t : ℂ) ^ 2 - z * t)
  have hf_cont : Continuous f := by fun_prop
  have hfc : LocallyIntegrableOn f (Ioi 0) :=
    hf_cont.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hf_exp : f =O[atTop] fun t : ℝ => Real.exp (-(a.re / 2) * t) := by
    refine Asymptotics.IsBigO.of_bound (Real.exp (z.re ^ 2 / (2 * a.re))) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht1
    have hre : (-a * (t : ℂ) ^ 2 - z * t).re = -a.re * t ^ 2 - z.re * t := by
      simp [← Complex.ofReal_pow]
    have hsq : t ≤ t ^ 2 := by nlinarith
    have hexp : -a.re * t ^ 2 - z.re * t ≤ z.re ^ 2 / (2 * a.re) + -(a.re / 2) * t := by
      have h0 : 0 ≤ a.re / 2 * (t + z.re / a.re) ^ 2 := by positivity
      have hid : a.re / 2 * (t + z.re / a.re) ^ 2 =
          a.re / 2 * t ^ 2 + z.re * t + z.re ^ 2 / (2 * a.re) := by field_simp; ring
      nlinarith
    rw [Complex.norm_exp, hre, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_le_exp.mpr hexp
  have hf_top : f =O[atTop] fun t : ℝ => t ^ (-(b₀.re + 1)) :=
    hf_exp.trans (isLittleO_exp_neg_mul_rpow_atTop (half_pos ha) _).isBigO
  have hf_bot : f =O[𝓝[>] (0 : ℝ)] fun t : ℝ => t ^ (-(0 : ℝ)) := by
    simp_rw [neg_zero, Real.rpow_zero]
    exact Asymptotics.isBigO_const_of_tendsto hf_cont.continuousWithinAt one_ne_zero
  have hm := (mellin_hasDerivAt_of_isBigO_rpow hfc hf_top (lt_add_one b₀.re) hf_bot hb₀).2
  simp only [mellin, smul_eq_mul] at hm
  refine hm.congr_deriv (setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_)
  rw [Complex.real_smul, Complex.ofReal_log ht.le]
  ring

/-- At `a = 1 / 2` (DLMF 12.5.1), differentiating
`b ↦ ∫ t in Ioi 0, (t : ℂ) ^ (b - 1) * exp (-t² / 2 - z t)` at `0 < b₀.re` inserts a factor
`Complex.log t` into the integrand, for every `z : ℂ`. -/
theorem hasDerivAt_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_left {b₀ : ℂ}
    (hb₀ : 0 < b₀.re) (z : ℂ) :
    HasDerivAt
      (fun b : ℂ =>
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-(t : ℂ) ^ 2 / 2 - z * t))
      (∫ t in Ioi (0 : ℝ),
        Complex.log t * (t : ℂ) ^ (b₀ - 1) * Complex.exp (-(t : ℂ) ^ 2 / 2 - z * t)) b₀ := by
  simpa only [neg_half_mul_sq_sub] using
    hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_left (a := 1 / 2) (by norm_num) hb₀ z

/-- For `0 < a.re` and every `z : ℂ`, the Mellin–Gaussian–Laplace integral is holomorphic in `b` on
the right half-plane `{b : ℂ | 0 < b.re}`. -/
theorem differentiableOn_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_left {a : ℂ} (ha : 0 < a.re)
    (z : ℂ) :
    DifferentiableOn ℂ
      (fun b : ℂ =>
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t))
      {b : ℂ | 0 < b.re} :=
  fun _ hb =>
    (hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_left ha hb z).differentiableAt
      |>.differentiableWithinAt

/-- At `a = 1 / 2` (DLMF 12.5.1), `b ↦ ∫ t in Ioi 0, (t : ℂ) ^ (b - 1) * exp (-t² / 2 - z t)` is
holomorphic on `{b : ℂ | 0 < b.re}` for every `z : ℂ`. -/
theorem differentiableOn_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_left (z : ℂ) :
    DifferentiableOn ℂ
      (fun b : ℂ =>
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-(t : ℂ) ^ 2 / 2 - z * t))
      {b : ℂ | 0 < b.re} :=
  fun _ hb =>
    (hasDerivAt_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_left hb z).differentiableAt
      |>.differentiableWithinAt

end TauCeti
