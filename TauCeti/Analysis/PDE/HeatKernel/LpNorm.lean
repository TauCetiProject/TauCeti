/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Basic
import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian

/-!
# Exact norms of the heat kernel

Raising a Gaussian to a positive power changes its time scale from `t` to `t / r`.
Its mass then gives the exact `Lʳ` norm
`(4πt)^(-(d/2)(1 - 1/r)) r^(-d/(2r))`. At `r = ∞`, the essential supremum is
the value at the origin. These formulas quantify the kernel constants in Young's
inequality for heat evolution.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A positive real power of the heat kernel is a multiple of the heat kernel
at time `t / r`. -/
theorem heatKernel_rpow {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : E) :
    heatKernel t x ^ r =
      (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2 * (r - 1)) *
        r ^ (-(Module.finrank ℝ E : ℝ) / 2) * heatKernel (t / r) x := by
  have hc : 0 < 4 * π * t := by positivity
  have htime : 4 * π * (t / r) = (4 * π * t) / r := by ring
  have he : (-‖x‖ ^ 2 / (4 * t)) * r = -‖x‖ ^ 2 / (4 * (t / r)) := by
    field_simp
  have hcoef : (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2 * (r - 1)) *
      r ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        ((4 * π * t) / r) ^ (-(Module.finrank ℝ E : ℝ) / 2) =
          (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2 * r) := by
    rw [div_rpow hc.le hr.le]
    rw [mul_assoc, mul_div_cancel₀ _ (by positivity)]
    rw [← rpow_add hc]
    congr 1
    ring
  simp only [heatKernel_apply]
  rw [mul_rpow (rpow_nonneg hc.le (-(Module.finrank ℝ E : ℝ) / 2))
      (exp_pos (-‖x‖ ^ 2 / (4 * t))).le, ← exp_mul, he,
    htime,
    ← rpow_mul hc.le, ← mul_assoc, hcoef]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The integral of a positive real power of the heat kernel. -/
@[simp]
theorem integral_heatKernel_rpow {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ∫ x : E, heatKernel t x ^ r =
      (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2 * (r - 1)) *
        r ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
  simp_rw [heatKernel_rpow ht hr, integral_const_mul, integral_heatKernel (div_pos ht hr),
    mul_one]

private theorem eLpNorm_heatKernel_eq_mul_gaussian {t : ℝ}
    (hb : 0 < ((1 / (4 * t) : ℝ) : ℂ).re) (r : ℝ≥0∞) :
    eLpNorm (heatKernel t : E → ℝ) r volume =
      ENNReal.ofReal ((4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)) *
        eLpNorm (SchwartzMap.gaussian (V := E) hb) r volume := by
  have ht : 0 < t := by
    simpa only [Complex.ofReal_re, one_div_pos,
      mul_pos_iff_of_pos_left (by norm_num : (0 : ℝ) < 4)] using hb
  have hn : eLpNorm (heatKernel t : E → ℝ) r volume =
      eLpNorm ((4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) •
        (SchwartzMap.gaussian (V := E) hb : E → ℂ)) r volume := by
    refine eLpNorm_congr_norm_ae
      (contDiff_heatKernel (k := ⊤) t).continuous.aestronglyMeasurable
      ((SchwartzMap.gaussian hb).continuous.const_smul _).aestronglyMeasurable
      (.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (heatKernel_pos ht x).le, Pi.smul_apply, norm_smul,
      Real.norm_of_nonneg (rpow_nonneg (by positivity) _),
      SchwartzMap.norm_gaussian_apply, Complex.ofReal_re, heatKernel_apply]
    congr 2
    ring
  rw [hn, eLpNorm_const_smul, ← ofReal_norm, Real.norm_of_nonneg (by positivity)]

/-- The exact finite, positive exponent `Lʳ` norm of the heat kernel. -/
@[simp]
theorem eLpNorm_heatKernel {t : ℝ} (ht : 0 < t) {r : ℝ≥0∞} (hr₀ : r ≠ 0) (hr : r ≠ ∞) :
    eLpNorm (heatKernel t : E → ℝ) r volume =
      ENNReal.ofReal ((4 * π * t) ^
        (-(Module.finrank ℝ E : ℝ) / 2 * (1 - 1 / r.toReal)) *
          r.toReal ^ (-(Module.finrank ℝ E : ℝ) / (2 * r.toReal))) := by
  have hrpos := ENNReal.toReal_pos hr₀ hr
  have hb : 0 < ((1 / (4 * t) : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    positivity
  have hc : 0 < 4 * π * t := by positivity
  have hbase : π / (1 / (4 * t) * r.toReal) = (4 * π * t) / r.toReal := by
    field_simp
  rw [eLpNorm_heatKernel_eq_mul_gaussian hb, SchwartzMap.eLpNorm_gaussian hb hr₀ hr,
    Complex.ofReal_re, hbase, ← ENNReal.ofReal_mul (by positivity),
    div_rpow hc.le hrpos.le, div_eq_mul_inv _ (r.toReal ^ _),
    ← rpow_neg hrpos.le, ← mul_assoc,
    ← rpow_add hc]
  congr 2 <;> congr 1 <;> field_simp
  ring

/-- The `L∞` norm of the heat kernel equals its value at the origin. -/
@[simp]
theorem eLpNorm_heatKernel_top {t : ℝ} (ht : 0 < t) :
    eLpNorm (heatKernel t : E → ℝ) ∞ volume =
      ENNReal.ofReal ((4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)) := by
  have hb : 0 < ((1 / (4 * t) : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    positivity
  rw [eLpNorm_heatKernel_eq_mul_gaussian hb, SchwartzMap.eLpNorm_gaussian_top hb, mul_one]

end TauCeti
