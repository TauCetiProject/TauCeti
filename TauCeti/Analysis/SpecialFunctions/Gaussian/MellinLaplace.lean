/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Mellin–Gaussian–Laplace integrals on the positive half-line

For `Re a > 0`, `Re b > 0`, and arbitrary `z : ℂ`, the half-line integral

  `∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t)`

converges absolutely: the quadratic decay `exp (-Re a · t²)` dominates the linear factor
`exp (-Re z · t)` at infinity regardless of the sign of `Re z`, while `Re b > 0` controls the power
singularity at the origin. At `a = 1 / 2`, this is the Laplace–Mellin integral kernel of Tricomi's
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
* `TauCeti.integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi`,
  `TauCeti.integral_cpow_mul_cexp_neg_mul_sq_div_two_sub_mul_Ioi`: positive-real scale change
  `v = c * u` (`0 < c`) on `(0, ∞)`, valid unconditionally for all complex parameters.
* `TauCeti.hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_right`,
  `TauCeti.differentiable_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_right`,
  `TauCeti.differentiable_integral_cpow_mul_cexp_neg_sq_div_two_sub_mul_Ioi_right`: differentiation
  under the integral sign and entireness in `z : ℂ`.
* `TauCeti.hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_left`,
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
theorem integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi {c : ℝ} (hc : 0 < c) (a b z : ℂ) :
    (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (b - 1) * Complex.exp (-a * ((c : ℂ) * u) ^ 2 - z * u)) =
      (c : ℂ) ^ (-b) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (b - 1) * Complex.exp (-a * (v : ℂ) ^ 2 - (z / c) * v) := by
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  let g : ℝ → ℂ := fun v => (v : ℂ) ^ (b - 1) * Complex.exp (-a * (v : ℂ) ^ 2 - (z / c) * v)
  have hsub := integral_comp_mul_left_Ioi' g 0 hc
  rw [mul_zero, Complex.real_smul] at hsub
  have hcongr : (∫ u in Ioi (0 : ℝ), g (c * u)) =
      (c : ℂ) ^ (b - 1) *
        ∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (b - 1) * Complex.exp (-a * ((c : ℂ) * u) ^ 2 - z * u) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_
    simp only [g, Complex.ofReal_mul]
    rw [Complex.mul_cpow_ofReal_nonneg hc.le hu.le (b - 1), mul_assoc]
    congr 2
    field_simp
  have hcb : (c : ℂ) * (c : ℂ) ^ (b - 1) = (c : ℂ) ^ b :=
    calc (c : ℂ) * (c : ℂ) ^ (b - 1)
        = (c : ℂ) ^ (1 : ℂ) * (c : ℂ) ^ (b - 1) := by rw [Complex.cpow_one]
      _ = (c : ℂ) ^ ((1 : ℂ) + (b - 1)) := (Complex.cpow_add _ _ hc0).symm
      _ = (c : ℂ) ^ b := by congr 1; ring
  rw [hcongr, ← mul_assoc, hcb] at hsub
  calc (∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (b - 1) * Complex.exp (-a * ((c : ℂ) * u) ^ 2 - z * u))
      = ((c : ℂ) ^ (-b) * (c : ℂ) ^ b) *
          ∫ u in Ioi (0 : ℝ),
            (u : ℂ) ^ (b - 1) * Complex.exp (-a * ((c : ℂ) * u) ^ 2 - z * u) := by
          rw [← Complex.cpow_add _ _ hc0, neg_add_cancel, Complex.cpow_zero, one_mul]
    _ = (c : ℂ) ^ (-b) *
          ((c : ℂ) ^ b * ∫ u in Ioi (0 : ℝ),
            (u : ℂ) ^ (b - 1) * Complex.exp (-a * ((c : ℂ) * u) ^ 2 - z * u)) := mul_assoc _ _ _
    _ = (c : ℂ) ^ (-b) * ∫ v in Ioi (0 : ℝ), g v := by rw [hsub]

/-- Positive-real rescaling `v = c * u` (`0 < c`) for the `a = 1 / 2` Mellin–Gaussian–Laplace
integral on `(0, ∞)`. -/
theorem integral_cpow_mul_cexp_neg_mul_sq_div_two_sub_mul_Ioi {c : ℝ} (hc : 0 < c) (b z : ℂ) :
    (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (b - 1) * Complex.exp (-((c : ℂ) * u) ^ 2 / 2 - z * u)) =
      (c : ℂ) ^ (-b) *
        ∫ v in Ioi (0 : ℝ),
          (v : ℂ) ^ (b - 1) * Complex.exp (-(v : ℂ) ^ 2 / 2 - (z / c) * v) := by
  have h := integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi hc (1 / 2) b z
  have hL : (∫ u in Ioi (0 : ℝ),
      (u : ℂ) ^ (b - 1) * Complex.exp (-((c : ℂ) * u) ^ 2 / 2 - z * u)) =
    ∫ u in Ioi (0 : ℝ),
      (u : ℂ) ^ (b - 1) * Complex.exp (-(1 / 2 : ℂ) * ((c : ℂ) * u) ^ 2 - z * u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    congr 2
    ring
  have hR : (∫ v in Ioi (0 : ℝ),
      (v : ℂ) ^ (b - 1) * Complex.exp (-(v : ℂ) ^ 2 / 2 - (z / c) * v)) =
    ∫ v in Ioi (0 : ℝ),
      (v : ℂ) ^ (b - 1) * Complex.exp (-(1 / 2 : ℂ) * (v : ℂ) ^ 2 - (z / c) * v) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    congr 2
    ring
  rw [hL, hR, h]

/-! ### Complex differentiability in the linear parameter `z` -/

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
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-(t : ℂ) ^ 2 / 2 - z * t) := by
  have heq : (fun z : ℂ =>
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-(t : ℂ) ^ 2 / 2 - z * t)) =
    fun z : ℂ =>
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-(1 / 2 : ℂ) * (t : ℂ) ^ 2 - z * t) := by
    ext z
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    congr 2
    ring
  rw [heq]
  exact differentiable_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_right (by norm_num) hb

/-! ### Complex differentiability in the exponent `b` -/

/-- Auxiliary uniform bound on `|log t| * t ^ (σ - 1)` for `σ ∈ (3 δ, 5 δ)` (`0 < δ`) across all
`0 < t`, avoiding logarithmic singularities by absorbing `|log t|` into small power shifts at both
`0` and `∞`. -/
private theorem abs_log_mul_rpow_le_add {δ σ t : ℝ} (hδ : 0 < δ) (hlo : 3 * δ < σ)
    (hhi : σ < 5 * δ) (ht : 0 < t) :
    |Real.log t| * t ^ (σ - 1) ≤ δ⁻¹ * t ^ (2 * δ - 1) + t ^ (5 * δ) := by
  rcases le_total t 1 with ht1 | ht1
  · have hlog_nonpos : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
    have hlog : |Real.log t| ≤ δ⁻¹ * t ^ (-δ) := by
      rw [abs_of_nonpos hlog_nonpos, le_inv_mul_iff₀ hδ]
      have hrpow_pos : 0 < t ^ (-δ) := Real.rpow_pos_of_pos ht (-δ)
      have h1 := Real.log_le_sub_one_of_pos hrpow_pos
      rw [Real.log_rpow ht] at h1
      linarith
    have hrpow : t ^ (σ - 1) ≤ t ^ (3 * δ - 1) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
    have hprod : |Real.log t| * t ^ (σ - 1) ≤ δ⁻¹ * t ^ (2 * δ - 1) := by
      calc |Real.log t| * t ^ (σ - 1)
          ≤ (δ⁻¹ * t ^ (-δ)) * t ^ (3 * δ - 1) :=
            mul_le_mul hlog hrpow (Real.rpow_nonneg ht.le _) (by positivity)
        _ = δ⁻¹ * (t ^ (-δ) * t ^ (3 * δ - 1)) := mul_assoc _ _ _
        _ = δ⁻¹ * t ^ (2 * δ - 1) := by
            rw [← Real.rpow_add ht]
            congr 2
            ring
    exact hprod.trans (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))
  · have hlog : |Real.log t| ≤ t ^ (1 : ℝ) := by
      rw [abs_of_nonneg (Real.log_nonneg ht1), Real.rpow_one]
      linarith [Real.log_le_sub_one_of_pos ht]
    have hrpow : t ^ (σ - 1) ≤ t ^ (5 * δ - 1) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    have hprod : |Real.log t| * t ^ (σ - 1) ≤ t ^ (5 * δ) := by
      calc |Real.log t| * t ^ (σ - 1)
          ≤ t ^ (1 : ℝ) * t ^ (5 * δ - 1) :=
            mul_le_mul hlog hrpow (Real.rpow_nonneg ht.le _) (by positivity)
        _ = t ^ (5 * δ) := by
            rw [← Real.rpow_add ht]
            congr 1
            ring
    exact hprod.trans (le_add_of_nonneg_left (by positivity))

/-- Differentiating the Mellin–Gaussian–Laplace integral with respect to `b` at `0 < b₀.re` inserts
a factor `Complex.log t` into the integrand, for `0 < a.re` and every `z : ℂ`. -/
theorem hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_left {a b₀ : ℂ} (ha : 0 < a.re)
    (hb₀ : 0 < b₀.re) (z : ℂ) :
    HasDerivAt
      (fun b : ℂ =>
        ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t))
      (∫ t in Ioi (0 : ℝ),
        Complex.log t * (t : ℂ) ^ (b₀ - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t)) b₀ := by
  set δ := b₀.re / 4 with hδ_def
  have hδ : 0 < δ := by positivity
  have hball : Metric.ball b₀ δ ∈ 𝓝 b₀ := Metric.ball_mem_nhds b₀ hδ
  have hbint : Integrable
      (fun t : ℝ => (δ⁻¹ * t ^ (2 * δ - 1) + t ^ (5 * δ)) *
        Real.exp (-a.re * t ^ 2 - z.re * t))
      (volume.restrict (Ioi 0)) := by
    have h1 := (integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi ha
      (by linarith : -1 < 2 * δ - 1) z.re).const_mul δ⁻¹
    have h2 := integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi ha
      (by linarith : -1 < 5 * δ) z.re
    exact IntegrableOn.congr_fun (h1.add h2) (fun t _ => by simp only [Pi.add_apply]; ring)
      measurableSet_Ioi
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun b (t : ℝ) => (t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t))
    (F' := fun b (t : ℝ) =>
      Complex.log t * (t : ℂ) ^ (b - 1) * Complex.exp (-a * (t : ℂ) ^ 2 - z * t))
    (bound := fun t : ℝ =>
      (δ⁻¹ * t ^ (2 * δ - 1) + t ^ (5 * δ)) * Real.exp (-a.re * t ^ 2 - z.re * t))
    hball (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi ha hb₀ z)
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hbint ?_
  · exact h.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) b hb
    rw [Metric.mem_ball, dist_eq_norm] at hb
    have hre := abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm (b - b₀)) hb)
    rw [Complex.sub_re] at hre
    have hlo : 3 * δ < b.re := by linarith [hδ_def, hre.1]
    have hhi : b.re < 5 * δ := by linarith [hδ_def, hre.2]
    rw [mul_assoc, norm_mul, norm_cpow_mul_cexp_neg_mul_sq_sub_mul a b z ht,
      ← Complex.ofReal_log ht.le, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (abs_log_mul_rpow_le_add hδ hlo hhi ht) (Real.exp_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) b _
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    have hpow : HasDerivAt (fun w : ℂ => (t : ℂ) ^ (w - 1))
        ((t : ℂ) ^ (b - 1) * Complex.log t * 1) b :=
      ((hasDerivAt_id b).sub_const 1).const_cpow (Or.inl ht0)
    refine (hpow.mul_const (Complex.exp (-a * (t : ℂ) ^ 2 - z * t))).congr_deriv ?_
    ring

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
      {b : ℂ | 0 < b.re} := by
  refine (differentiableOn_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_left (a := 1 / 2)
    (by norm_num) z).congr fun _ _ => setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  congr 2
  ring

end TauCeti
