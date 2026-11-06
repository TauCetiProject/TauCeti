/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Sine-compensated Laplace integrals

The kernel `exp (-a * x) - 1 + a * sin x` vanishes quadratically at zero.
Its power-weighted integral supplies the Laplace exponent of a totally skewed stable law.
Gamma mixtures reduce the calculation to Mellin integrals of rational functions.
-/

public section

noncomputable section

open MeasureTheory Real Set Filter
open scoped Topology

namespace TauCeti

/-- The Laplace transform of the real sine-compensated exponential kernel, for
`0 < s` and `0 < s + a`. -/
theorem integral_Ioi_exp_neg_mul_mul_exp_sub_one_add_sin {s a : ℝ}
    (hs : 0 < s) (ha : 0 < s + a) :
    ∫ x in Ioi (0 : ℝ), exp (-(x * s)) * (exp (-a * x) - 1 + a * sin x) =
      (s + a)⁻¹ - s⁻¹ + a / (1 + s ^ 2) := by
  have hC : (-s + Complex.I : ℂ).re < 0 := by simpa using hs
  have hformC (x : ℝ) : (Complex.exp ((-s + Complex.I) * x)).im =
      exp (-s * x) * sin x := by simp [Complex.exp_im]
  have hi : IntegrableOn (fun x : ℝ ↦ exp (-s * x) * sin x) (Ioi 0) := by
    simpa only [RCLike.im_to_complex, hformC] using
      (integrableOn_exp_mul_complex_Ioi hC 0).im
  have heq : ∫ x in Ioi (0 : ℝ), exp (-s * x) * sin x = (1 + s ^ 2)⁻¹ := by
    have h := congrArg Complex.im (integral_exp_mul_complex_Ioi hC 0)
    rw [← RCLike.im_to_complex, ← integral_im (integrableOn_exp_mul_complex_Ioi hC 0)] at h
    simp only [RCLike.im_to_complex, hformC] at h
    simpa [Complex.div_im, Complex.normSq_apply, pow_two, div_eq_mul_inv, add_comm] using h
  have hexp := integrableOn_exp_mul_Ioi (a := -(s + a)) (by linarith) 0
  have hbase := integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0
  have hform (x : ℝ) : exp (-(x * s)) * (exp (-a * x) - 1 + a * sin x) =
      exp (-(s + a) * x) - exp (-s * x) + a * (exp (-s * x) * sin x) := by
    have he : -(x * s) + -a * x = -(s + a) * x := by ring
    rw [mul_add, mul_sub, ← exp_add, he]
    simp only [neg_mul, mul_comm x s]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ ↦ hform x),
    integral_add (hexp.sub' hbase) (hi.const_mul a), integral_sub hexp hbase,
    integral_const_mul, integral_exp_mul_Ioi (by linarith : -(s + a) < 0) 0,
    integral_exp_mul_Ioi (by linarith : -s < 0) 0, heq]
  simp only [mul_zero, exp_zero, neg_div, div_neg, one_div, neg_neg]
  ring

/-- The Mellin integral of the rational sine-compensated Laplace transform, away from
exponent one. The cancellations at zero and infinity permit every `0 < α < 2`. -/
theorem integral_rpow_mul_inv_add_sub_inv_add_div_one_add_sq {α a : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (hα1 : α ≠ 1) (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), x ^ α * ((x + a)⁻¹ - x⁻¹ + a / (1 + x ^ 2)) =
      -a ^ α * (π / sin (π * α)) + a * (π / (2 * cos (π * α / 2))) := by
  rcases hα1.lt_or_gt with h1 | h1
  · -- Below one, the two separate Mellin integrals converge.
    have h0 : 0 < α + 1 := by linarith
    have h2 : α + 1 < 2 := by linarith
    have hsin : sin (π * (α + 1) / 2) = cos (π * α / 2) := by
      have he : π * (α + 1) / 2 = π * α / 2 + π / 2 := by ring
      rw [he, sin_add_pi_div_two]
    calc
      _ = ∫ x in Ioi (0 : ℝ), -a * (x ^ (α - 1) / (x + a)) +
          a * (x ^ (α + 1 - 1) / (x ^ 2 + 1 ^ 2)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
        rw [rpow_sub_one hx.ne', add_sub_cancel_right, one_pow]
        field_simp
        ring
      _ = _ := by
        rw [integral_add ((integrableOn_rpow_div_add α a hα h1 ha).const_mul (-a))
          ((integrableOn_rpow_div_sq_add_sq h0 h2 one_ne_zero).const_mul a),
          integral_const_mul, integral_const_mul, integral_rpow_div_add α a hα h1 ha,
          integral_rpow_div_sq_add_sq h0 h2 one_ne_zero, abs_one, one_rpow, hsin,
          rpow_sub_one ha.ne']
        field_simp
  · -- Above one, cancel the linear tail before separating the integrals.
    have h0 : 0 < α - 1 := by linarith
    have h2 : α - 1 < 2 := by linarith
    have hsin : sin (π * (α - 1) / 2) = -cos (π * α / 2) := by
      have he : π * (α - 1) / 2 = π * α / 2 - π / 2 := by ring
      rw [he, sin_sub_pi_div_two]
    have hsin' : sin (π * (α - 1)) = -sin (π * α) := by
      have he : π * (α - 1) = π * α - π := by ring
      rw [he, sin_sub_pi]
    calc
      _ = ∫ x in Ioi (0 : ℝ), a ^ 2 * (x ^ (α - 1 - 1) / (x + a)) -
          a * (x ^ (α - 1 - 1) / (x ^ 2 + 1 ^ 2)) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x (hx : 0 < x) ↦ ?_
        have hp : x ^ α = x ^ (α - 1 - 1) * x ^ 2 := by
          rw [← rpow_natCast, ← rpow_add hx]
          congr 1
          norm_num
          ring
        rw [hp, one_pow]
        field_simp
        ring
      _ = _ := by
        rw [integral_sub ((integrableOn_rpow_div_add (α - 1) a h0 (by linarith) ha).const_mul _)
          ((integrableOn_rpow_div_sq_add_sq h0 h2 one_ne_zero).const_mul a),
          integral_const_mul, integral_const_mul,
          integral_rpow_div_add (α - 1) a h0 (by linarith) ha,
          integral_rpow_div_sq_add_sq h0 h2 one_ne_zero, abs_one, one_rpow, hsin, hsin']
        have hp : a ^ 2 * a ^ (α - 1 - 1) = a ^ α := by
          rw [← rpow_natCast, ← rpow_add ha]
          congr 1
          norm_num
          ring
        rw [← mul_assoc, hp]
        ring

/-- At exponent one, the rational compensated Laplace integral is logarithmic. -/
theorem integral_mul_inv_add_sub_inv_add_div_one_add_sq {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0 : ℝ), x * ((x + a)⁻¹ - x⁻¹ + a / (1 + x ^ 2)) = a * log a := by
  -- This logarithmic primitive has a finite limit at both ends of the half-line.
  let F : ℝ → ℝ := fun x ↦ a / 2 * log (1 + x ^ 2) - a * log (x + a)
  have hpos (x : ℝ) : 1 + x ^ 2 ≠ 0 := by positivity
  have hcont : ContinuousWithinAt F (Ici 0) 0 := by
    apply ContinuousAt.continuousWithinAt
    unfold F
    fun_prop (disch := positivity)
  have hderiv (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      HasDerivAt F (x * ((x + a)⁻¹ - x⁻¹ + a / (1 + x ^ 2))) x := by
    have hx : 0 < x := hx
    have h1 := ((hasDerivAt_pow 2 x).const_add 1).log (hpos x)
    have h2 := ((hasDerivAt_id x).add_const a).log (by positivity : x + a ≠ 0)
    convert! (h1.const_mul (a / 2)).sub (h2.const_mul a) using 1
    simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp
    ring
  -- Bound the rational derivative by an integrable Cauchy kernel.
  have hint : IntegrableOn
      (fun x : ℝ ↦ x * ((x + a)⁻¹ - x⁻¹ + a / (1 + x ^ 2))) (Ioi 0) := by
    have hb := (integrableOn_rpow_div_sq_add_sq (s := 1) (by norm_num) (by norm_num)
      one_ne_zero).const_mul ((a + a⁻¹) * a)
    refine hb.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x (hx : 0 < x)
    have hf : x * ((x + a)⁻¹ - x⁻¹ + a / (1 + x ^ 2)) =
        a / (1 + x ^ 2) * ((a * x - 1) / (x + a)) := by field_simp; ring
    rw [hf, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < a / (1 + x ^ 2))]
    have hle : |(a * x - 1) / (x + a)| ≤ a + a⁻¹ := by
      rw [abs_div, abs_of_pos (by positivity : 0 < x + a), div_le_iff₀ (by positivity)]
      have hi : 0 ≤ a⁻¹ * x := by positivity
      rw [abs_le]
      constructor <;> field_simp <;> nlinarith [sq_nonneg a, mul_nonneg ha.le hx.le]
    calc
      _ ≤ a / (1 + x ^ 2) * (a + a⁻¹) := mul_le_mul_of_nonneg_left hle (by positivity)
      _ = _ := by simp; ring
  -- Combine the logarithms into a ratio tending to one; their separate limits diverge.
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hratio : Tendsto (fun x : ℝ ↦ (1 + x⁻¹ ^ 2) / (1 + a * x⁻¹) ^ 2)
        atTop (𝓝 1) := by
      simpa only [Pi.div_def, zero_pow two_ne_zero, add_zero, mul_zero, one_pow, div_one]
        using ((tendsto_inv_atTop_zero.pow 2).const_add 1).div
        ((tendsto_inv_atTop_zero.const_mul a).const_add 1 |>.pow 2) (by norm_num)
    have hlog := ((continuousAt_log one_ne_zero).tendsto.comp hratio).const_mul (a / 2)
    simp only [log_one, mul_zero] at hlog
    apply hlog.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x (hx : 0 < x)
    have hxa : x + a ≠ 0 := by positivity
    have hr : (1 + x⁻¹ ^ 2) / (1 + a * x⁻¹) ^ 2 = (1 + x ^ 2) / (x + a) ^ 2 := by
      field_simp
      ring
    simp only [Function.comp_apply]
    rw [hr, log_div (hpos x) (pow_ne_zero 2 hxa), log_pow]
    dsimp [F]
    ring
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  simp [F]

end TauCeti
