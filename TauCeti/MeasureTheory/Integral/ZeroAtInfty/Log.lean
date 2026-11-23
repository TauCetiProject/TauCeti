/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Log
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Weighted logarithmic integrals of functions vanishing at infinity

For a continuous function `f : C₀(Ω, E)` vanishing at infinity, a threshold `δ > 0`, and an
integrable nonnegative weight `w` of total mass `∫ w ∂μ = α > 0`, this file develops the
measure-theoretic properties of the clipped logarithmic envelope
`ZeroAtInftyContinuousMap.logMaxDiv`:

* `ZeroAtInftyContinuousMap.integrable_logMaxDiv`: when `[R1Space Ω]` and `μ` is finite on
  compact sets (`[IsFiniteMeasureOnCompacts μ]`), `f.logMaxDiv δ` is `μ`-integrable;
* `ZeroAtInftyContinuousMap.integrable_logMaxDiv_mul`: `(f.logMaxDiv δ ·) * w` is `μ`-integrable
  for any `μ`-integrable `w`;
* `ZeroAtInftyContinuousMap.integral_log_max_mul_eq`: the weighted splitting identity
  `∫ Real.log (max ‖f s‖ δ) * w s ∂μ = (∫ Real.log δ * w s ∂μ) + (∫ f.logMaxDiv δ s * w s ∂μ)`;
* `ZeroAtInftyContinuousMap.exp_integral_log_max_le_rpow`: weighted logarithmic Jensen inequality
  `exp (∫ Real.log (max ‖f s‖ δ) * w s ∂μ) ≤ (α⁻¹ * ∫ ‖f s‖ * w s ∂μ + δ) ^ α`.
-/

public section

namespace ZeroAtInftyContinuousMap

open MeasureTheory
open scoped ENNReal ZeroAtInfty

/-- For `δ > 0` and `[R1Space Ω]`, the clipped logarithmic envelope `logMaxDiv f δ` is integrable
with respect to any measure `μ` finite on compact sets. -/
theorem integrable_logMaxDiv {Ω E : Type*} [TopologicalSpace Ω] [R1Space Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasureOnCompacts μ]
    [SeminormedAddCommGroup E] (f : C₀(Ω, E)) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (logMaxDiv f δ) μ :=
  (continuous_logMaxDiv f hδ).integrable_of_hasCompactSupport (hasCompactSupport_logMaxDiv f hδ)

/-- For `δ > 0` and an integrable weight `w`, `(logMaxDiv f δ ·) * w` is integrable. -/
theorem integrable_logMaxDiv_mul {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : C₀(Ω, E)) {δ : ℝ}
    (hδ : 0 < δ) {w : Ω → ℝ} (hw_int : Integrable w μ) :
    Integrable (fun s ↦ logMaxDiv f δ s * w s) μ := by
  refine hw_int.bdd_mul (c := Real.log (max ‖f‖ δ / δ))
    (continuous_logMaxDiv f hδ).aestronglyMeasurable (ae_of_all _ fun s ↦ ?_)
  rw [Real.norm_of_nonneg (logMaxDiv_nonneg f hδ s), logMaxDiv_def]
  exact Real.log_le_log (div_pos (hδ.trans_le (le_max_right _ _)) hδ)
    (div_le_div_of_nonneg_right (max_le_max (norm_coe_le_norm f s) le_rfl) hδ.le)

/-- Splitting identity for a clipped weighted logarithmic integral of `f : C₀(Ω, E)` with
threshold `δ > 0` and integrable weight `w`:
`∫ Real.log (max ‖f s‖ δ) * w s ∂μ = (∫ Real.log δ * w s ∂μ) + (∫ f.logMaxDiv δ s * w s ∂μ)`. -/
theorem integral_log_max_mul_eq {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : C₀(Ω, E)) {δ : ℝ}
    (hδ : 0 < δ) {w : Ω → ℝ} (hw_int : Integrable w μ) :
    (∫ s, Real.log (max ‖f s‖ δ) * w s ∂μ) =
      (∫ s, Real.log δ * w s ∂μ) + (∫ s, logMaxDiv f δ s * w s ∂μ) := by
  rw [← integral_add (hw_int.const_mul _) (integrable_logMaxDiv_mul f hδ hw_int)]
  refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
  dsimp only; rw [← add_mul, log_add_logMaxDiv f hδ]

/-- Weighted logarithmic mean bound for a clipped `C₀(Ω, E)` function: for a threshold `δ > 0`
and an integrable nonnegative weight `w` of total mass `∫ w ∂μ = α > 0`,
`exp (∫ Real.log (max ‖f s‖ δ) * w s ∂μ) ≤ (α⁻¹ * ∫ ‖f s‖ * w s ∂μ + δ) ^ α`. -/
theorem exp_integral_log_max_le_rpow {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : C₀(Ω, E))
    {w : Ω → ℝ} {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hw_int : Integrable w μ)
    (hw_nonneg : ∀ s, 0 ≤ w s) (hw_sum : ∫ s, w s ∂μ = α) :
    Real.exp (∫ s, Real.log (max ‖f s‖ δ) * w s ∂μ) ≤ (α⁻¹ * (∫ s, ‖f s‖ * w s ∂μ) + δ) ^ α := by
  have hw_ae : AEMeasurable (fun s ↦ ENNReal.ofReal (w s)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hw_int.aemeasurable
  have hw_lt : ∀ᵐ s ∂μ, ENNReal.ofReal (w s) < ∞ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  let ν : Measure Ω := (ENNReal.ofReal α)⁻¹ • μ.withDensity (fun s ↦ ENNReal.ofReal (w s))
  have : IsProbabilityMeasure ν := ⟨by
    simp only [ν, _root_.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hw_int (ae_of_all _ hw_nonneg), hw_sum,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hα).ne' ENNReal.ofReal_ne_top]⟩
  have hmax_int : Integrable (fun s ↦ max ‖f s‖ δ * w s) μ :=
    hw_int.bdd_mul ((map_continuous f).norm.max continuous_const).aestronglyMeasurable
      (ae_of_all _ fun s ↦ by
        rw [Real.norm_of_nonneg (hδ.le.trans (le_max_right _ _))]
        exact max_le_max (norm_coe_le_norm f s) le_rfl)
  have hlog_int : Integrable (fun s ↦ Real.log (max ‖f s‖ δ) * w s) μ := by
    rw [show (fun s ↦ Real.log (max ‖f s‖ δ) * w s) =
        fun s ↦ Real.log δ * w s + logMaxDiv f δ s * w s by
      ext s; rw [← add_mul, log_add_logMaxDiv f hδ]]
    exact (hw_int.const_mul _).add (integrable_logMaxDiv_mul f hδ hw_int)
  have hto_int {u : Ω → ℝ} (hu : Integrable (fun s ↦ u s * w s) μ) : Integrable u ν :=
    ((integrable_withDensity_iff_integrable_smul₀' hw_ae hw_lt).2 (by
      simpa only [ENNReal.toReal_ofReal (hw_nonneg _), smul_eq_mul, mul_comm (w _)] using hu))
      |>.smul_measure (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hα).ne')
  have hjensen : (∫ s, Real.log (max ‖f s‖ δ) ∂ν) ≤ Real.log (∫ s, max ‖f s‖ δ ∂ν) :=
    (strictConcaveOn_log_Ioi.concaveOn.subset (Set.Ici_subset_Ioi.2 hδ)
      (convex_Ici δ)).le_map_integral
      (Real.continuousOn_log.mono fun _ hx ↦ (hδ.trans_le hx).ne')
      isClosed_Ici (ae_of_all _ fun s ↦ le_max_right _ _) (hto_int hmax_int) (hto_int hlog_int)
  have hint_eq (u : Ω → ℝ) : ∫ s, u s ∂ν = α⁻¹ * ∫ s, u s * w s ∂μ := by
    simp only [ν, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hα.le]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hw_ae hw_lt]
    simp_rw [ENNReal.toReal_ofReal (hw_nonneg _), smul_eq_mul, mul_comm (w _)]
  rw [hint_eq, hint_eq] at hjensen
  have hmax_pos : 0 < α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ := hδ.trans_le <| by
    rw [le_inv_mul_iff₀ hα, mul_comm α δ, ← hw_sum, ← integral_const_mul]
    exact integral_mono (hw_int.const_mul δ) hmax_int fun s ↦
      mul_le_mul_of_nonneg_right (le_max_right _ _) (hw_nonneg s)
  have hf_int : Integrable (fun s ↦ ‖f s‖ * w s) μ := hw_int.bdd_mul
    (map_continuous f).norm.aestronglyMeasurable
    (ae_of_all _ fun s ↦ by rw [norm_norm]; exact norm_coe_le_norm f s)
  have hmax_le : α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ ≤ α⁻¹ * (∫ s, ‖f s‖ * w s ∂μ) + δ := by
    have hint : ∫ s, max ‖f s‖ δ * w s ∂μ ≤ (∫ s, ‖f s‖ * w s ∂μ) + δ * α := by
      rw [show (∫ s, ‖f s‖ * w s ∂μ) + δ * α = ∫ s, (‖f s‖ * w s + δ * w s) ∂μ by
        rw [integral_add hf_int (hw_int.const_mul δ), integral_const_mul, hw_sum]]
      refine integral_mono hmax_int (hf_int.add (hw_int.const_mul δ)) fun s ↦ ?_
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right
        (max_le (le_add_of_nonneg_right hδ.le) (le_add_of_nonneg_left (norm_nonneg _)))
        (hw_nonneg s)
    refine (mul_le_mul_of_nonneg_left hint (inv_pos.2 hα).le).trans_eq ?_
    rw [mul_add, mul_left_comm, inv_mul_cancel₀ hα.ne', mul_one]
  have hexp : Real.exp (∫ s, Real.log (max ‖f s‖ δ) * w s ∂μ) ≤
      (α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ) ^ α := by
    rw [Real.rpow_def_of_pos hmax_pos, mul_comm _ α]
    exact Real.exp_le_exp.2 ((inv_mul_le_iff₀ hα).1 hjensen)
  exact hexp.trans (Real.rpow_le_rpow hmax_pos.le hmax_le hα.le)

end ZeroAtInftyContinuousMap
