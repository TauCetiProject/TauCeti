/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.HeatKernel.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

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
    show 4 * π * (t / r) = (4 * π * t) / r by ring,
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

/-- The exact finite, positive exponent `Lʳ` norm of the heat kernel. -/
@[simp]
theorem eLpNorm_heatKernel {t : ℝ} (ht : 0 < t) {r : ℝ≥0∞} (hr₀ : r ≠ 0) (hr : r ≠ ∞) :
    eLpNorm (heatKernel t : E → ℝ) r volume =
      ENNReal.ofReal ((4 * π * t) ^
        (-(Module.finrank ℝ E : ℝ) / 2 * (1 - 1 / r.toReal)) *
          r.toReal ^ (-(Module.finrank ℝ E : ℝ) / (2 * r.toReal))) := by
  have hrpos := ENNReal.toReal_pos hr₀ hr
  have hm : AEStronglyMeasurable (heatKernel t : E → ℝ) volume :=
    (contDiff_heatKernel (k := ⊤) t).continuous.aestronglyMeasurable
  have hi : Integrable (fun x : E => heatKernel t x ^ r.toReal) := by
    simp_rw [heatKernel_rpow ht hrpos]
    exact (integrable_heatKernel (div_pos ht hrpos)).const_mul _
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hr₀ hr hm]
  have hn (x : E) : ‖heatKernel t x‖ₑ ^ r.toReal =
      ENNReal.ofReal (heatKernel t x ^ r.toReal) := by
    rw [Real.eNorm_eq_ofReal (heatKernel_pos ht x).le,
      ENNReal.ofReal_rpow_of_pos (heatKernel_pos ht x)]
  simp_rw [hn]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
      (.of_forall fun x => (rpow_pos_of_pos (heatKernel_pos ht x) _).le),
    integral_heatKernel_rpow ht hrpos, ENNReal.ofReal_rpow_of_pos (by positivity),
    mul_rpow (by positivity) (by positivity), ← rpow_mul (by positivity : 0 ≤ 4 * π * t),
    ← rpow_mul hrpos.le]
  congr 2 <;> congr 1 <;> field_simp

/-- The `L∞` norm of the heat kernel equals its value at the origin. -/
@[simp]
theorem eLpNorm_heatKernel_top {t : ℝ} (ht : 0 < t) :
    eLpNorm (heatKernel t : E → ℝ) ∞ volume =
      ENNReal.ofReal ((4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)) := by
  apply le_antisymm
  · simpa using eLpNorm_heatKernel_le (E := E) ht (q := ∞) le_top
  · have hm := (contDiff_heatKernel (E := E) (k := ⊤) t).continuous
    have hclosed : IsClosed {x : E | ‖heatKernel t x‖ₑ ≤
        eLpNormEssSup (heatKernel t : E → ℝ) volume} :=
      isClosed_le hm.eNorm continuous_const
    have h := hclosed.closure_subset
      (volume.dense_of_ae (eNorm_ae_le_eLpNormEssSup (heatKernel t : E → ℝ) volume) (0 : E))
    rw [← eLpNorm_exponent_top hm.aestronglyMeasurable] at h
    simpa [heatKernel_apply, Real.eNorm_eq_ofReal (by positivity :
      0 ≤ (4 * π * t) ^ (-(Module.finrank ℝ E : ℝ) / 2))] using h

end TauCeti
