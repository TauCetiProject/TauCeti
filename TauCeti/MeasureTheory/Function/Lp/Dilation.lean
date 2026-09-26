/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
-- `TauCeti.MeasureTheory.Integral.Dilation` is imported publicly: `TauCeti.lintegral_comp_inv_smul`
-- is the `∫⁻` form of the statement below, so the two belong together for a reader of either.
public import TauCeti.MeasureTheory.Integral.Dilation

/-!
# Dilation scaling of the `Lᵖ` seminorm

Dilating the variable of a function on a finite-dimensional real normed space `E` by `r⁻¹`, for
`r > 0`, multiplies its `Lᵖ` seminorm against an additive Haar measure by `r ^ (n / p)`, where
`n` is the dimension of `E` and `0 < p < ∞`. This is the `eLpNorm` form of the lower Lebesgue
integral law `TauCeti.lintegral_comp_inv_smul`, obtained by applying the latter to
`y ↦ ‖f y‖ₑ ^ p` and taking a `p`-th root.

## Main declarations

* `TauCeti.eLpNorm_comp_inv_smul`: `‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p`.
-/

public section

namespace TauCeti

open MeasureTheory Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {G : Type*} [NormedAddCommGroup G]

/-- **Dilation scaling of the `Lᵖ` seminorm:** `‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p`, where
`n` is the dimension of the ambient space. -/
theorem eLpNorm_comp_inv_smul (f : E → G) {r : ℝ} (hr : 0 < r) {p : ℝ≥0∞} (hp₀ : p ≠ 0)
    (hp : p ≠ ∞) :
    eLpNorm (fun x => f (r⁻¹ • x)) p μ =
      ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / p.toReal)) * eLpNorm f p μ := by
  have ht : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp
  have hr' : r⁻¹ ≠ 0 := inv_ne_zero hr.ne'
  -- Dilating the variable preserves a.e. strong measurability, in both directions, because it
  -- transports the Haar measure to a positive multiple of itself.
  have hiff : AEStronglyMeasurable (fun x => f (r⁻¹ • x)) μ ↔ AEStronglyMeasurable f μ := by
    have he : MeasurableEmbedding (fun x : E => r⁻¹ • x) :=
      (Homeomorph.smul (isUnit_iff_ne_zero.2 hr').unit).toMeasurableEquiv.measurableEmbedding
    have hc : ENNReal.ofReal |(r⁻¹ ^ finrank ℝ E)⁻¹| ≠ 0 :=
      (ENNReal.ofReal_pos.2 (abs_pos.2 (inv_ne_zero (pow_ne_zero _ hr')))).ne'
    have hcomp : AEStronglyMeasurable (f ∘ fun x : E => r⁻¹ • x) μ ↔
        AEStronglyMeasurable f μ := by
      rw [← he.aestronglyMeasurable_map_iff, Measure.map_addHaar_smul μ hr']
      simp only [AEStronglyMeasurable, Measure.ae_ennreal_smul_measure_eq hc]
    exact hcomp
  by_cases hf : AEStronglyMeasurable f μ
  case neg =>
    rw [eLpNorm_of_not_aestronglyMeasurable hf,
      eLpNorm_of_not_aestronglyMeasurable fun h => hf (hiff.1 h),
      ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
  have key := lintegral_comp_inv_smul μ (fun y => ‖f y‖ₑ ^ p.toReal) hr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp (hiff.2 hf),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp hf,
    key, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  have hpow : ((r ^ finrank ℝ E : ℝ)) ^ (1 / p.toReal) = r ^ ((finrank ℝ E : ℝ) / p.toReal) := by
    rw [← Real.rpow_natCast r (finrank ℝ E), ← Real.rpow_mul hr.le]
    ring_nf
  congr 1
  rw [← hpow]
  exact ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < r ^ finrank ℝ E)

end TauCeti
