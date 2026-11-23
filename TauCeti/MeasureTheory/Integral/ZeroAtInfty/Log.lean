/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Log
import Mathlib.Analysis.Convex.Integral

/-!
# Weighted logarithmic integrals of functions vanishing at infinity

For a continuous function `f : C₀(Ω, E)` vanishing at infinity, a threshold `δ > 0`, and an
almost everywhere nonnegative integrable weight `w` of total mass `∫ w ∂μ = α > 0`, this file
develops the measure-theoretic properties of the clipped logarithmic envelope
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
    Integrable (fun s ↦ logMaxDiv f δ s * w s) μ :=
  hw_int.bdd_mul (c := Real.log (max ‖f‖ δ / δ))
    (continuous_logMaxDiv f hδ).aestronglyMeasurable (ae_of_all _ fun s ↦ by
      rw [Real.norm_of_nonneg (logMaxDiv_nonneg f hδ s), logMaxDiv_def]
      exact Real.log_le_log (div_pos (hδ.trans_le (le_max_right _ _)) hδ)
        (div_le_div_of_nonneg_right (max_le_max (norm_coe_le_norm f s) le_rfl) hδ.le))

private theorem log_max_mul_eq_add {Ω E : Type*} [TopologicalSpace Ω]
    [SeminormedAddCommGroup E] (f : C₀(Ω, E)) {δ : ℝ} (hδ : 0 < δ) (w : Ω → ℝ) :
    (fun s ↦ Real.log (max ‖f s‖ δ) * w s) =
      fun s ↦ Real.log δ * w s + logMaxDiv f δ s * w s :=
  funext fun s ↦ by rw [← add_mul, log_add_logMaxDiv f hδ]

/-- Splitting identity for a clipped weighted logarithmic integral of `f : C₀(Ω, E)` with
threshold `δ > 0` and integrable weight `w`:
`∫ Real.log (max ‖f s‖ δ) * w s ∂μ = (∫ Real.log δ * w s ∂μ) + (∫ f.logMaxDiv δ s * w s ∂μ)`. -/
theorem integral_log_max_mul_eq {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : C₀(Ω, E)) {δ : ℝ}
    (hδ : 0 < δ) {w : Ω → ℝ} (hw_int : Integrable w μ) :
    (∫ s, Real.log (max ‖f s‖ δ) * w s ∂μ) =
      (∫ s, Real.log δ * w s ∂μ) + (∫ s, logMaxDiv f δ s * w s ∂μ) := by
  rw [log_max_mul_eq_add f hδ w,
    integral_add (hw_int.const_mul _) (integrable_logMaxDiv_mul f hδ hw_int)]

section
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ) (α : ℝ)

private noncomputable def weightedProbMeasure : Measure Ω :=
  (ENNReal.ofReal α)⁻¹ • μ.withDensity (fun s ↦ ENNReal.ofReal (w s))

variable {μ w α}

private theorem isProbabilityMeasure_weightedProbMeasure (hα : 0 < α) (hw_int : Integrable w μ)
    (hw_nonneg : 0 ≤ᵐ[μ] w) (hw_sum : ∫ s, w s ∂μ = α) :
    IsProbabilityMeasure (weightedProbMeasure μ w α) :=
  ⟨by
    simp only [weightedProbMeasure, _root_.smul_apply, smul_eq_mul,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hw_int hw_nonneg, hw_sum,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hα).ne' ENNReal.ofReal_ne_top]⟩

private theorem integrable_weightedProbMeasure (hα : 0 < α) (hw_int : Integrable w μ)
    (hw_nonneg : 0 ≤ᵐ[μ] w) {u : Ω → ℝ} (hu : Integrable (fun s ↦ u s * w s) μ) :
    Integrable u (weightedProbMeasure μ w α) :=
  ((integrable_withDensity_iff_integrable_smul₀'
    (ENNReal.measurable_ofReal.comp_aemeasurable hw_int.aemeasurable)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
    (hu.congr (hw_nonneg.mono fun _ hs ↦ by
      simp [ENNReal.toReal_ofReal hs, mul_comm]))).smul_measure
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hα).ne')

private theorem integral_weightedProbMeasure (hα : 0 < α) (hw_int : Integrable w μ)
    (hw_nonneg : 0 ≤ᵐ[μ] w) (u : Ω → ℝ) :
    ∫ s, u s ∂(weightedProbMeasure μ w α) = α⁻¹ * ∫ s, u s * w s ∂μ := by
  simp only [weightedProbMeasure, integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hα.le]
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun s ↦ ENNReal.ofReal (w s))
    (ENNReal.measurable_ofReal.comp_aemeasurable hw_int.aemeasurable)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  exact congrArg (α⁻¹ * ·) (integral_congr_ae
    (hw_nonneg.mono fun _ hs ↦ by simp [ENNReal.toReal_ofReal hs, mul_comm]))

end

/-- Weighted logarithmic mean bound for a clipped `C₀(Ω, E)` function: for a threshold `δ > 0`
and an almost everywhere nonnegative integrable weight `w` of total mass `∫ w ∂μ = α > 0`,
`exp (∫ Real.log (max ‖f s‖ δ) * w s ∂μ) ≤ (α⁻¹ * ∫ ‖f s‖ * w s ∂μ + δ) ^ α`. -/
theorem exp_integral_log_max_le_rpow {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : C₀(Ω, E))
    {w : Ω → ℝ} {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hw_int : Integrable w μ)
    (hw_nonneg : 0 ≤ᵐ[μ] w) (hw_sum : ∫ s, w s ∂μ = α) :
    Real.exp (∫ s, Real.log (max ‖f s‖ δ) * w s ∂μ) ≤ (α⁻¹ * (∫ s, ‖f s‖ * w s ∂μ) + δ) ^ α := by
  have _ := isProbabilityMeasure_weightedProbMeasure hα hw_int hw_nonneg hw_sum
  have hmax_int : Integrable (fun s ↦ max ‖f s‖ δ * w s) μ :=
    hw_int.bdd_mul ((map_continuous f).norm.max continuous_const).aestronglyMeasurable
      (ae_of_all _ fun s ↦ by
        rw [Real.norm_of_nonneg (hδ.le.trans (le_max_right _ _))]
        exact max_le_max (norm_coe_le_norm f s) le_rfl)
  have hlog_int : Integrable (fun s ↦ Real.log (max ‖f s‖ δ) * w s) μ :=
    (log_max_mul_eq_add f hδ w).symm ▸
      (hw_int.const_mul _).add (integrable_logMaxDiv_mul f hδ hw_int)
  have hjensen : (∫ s, Real.log (max ‖f s‖ δ) ∂weightedProbMeasure μ w α) ≤
      Real.log (∫ s, max ‖f s‖ δ ∂weightedProbMeasure μ w α) :=
    (strictConcaveOn_log_Ioi.concaveOn.subset (Set.Ici_subset_Ioi.2 hδ)
      (convex_Ici δ)).le_map_integral (Real.continuousOn_log.mono fun _ hx ↦ (hδ.trans_le hx).ne')
      isClosed_Ici (ae_of_all _ fun _ ↦ le_max_right _ _)
      (integrable_weightedProbMeasure hα hw_int hw_nonneg hmax_int)
      (integrable_weightedProbMeasure hα hw_int hw_nonneg hlog_int)
  rw [integral_weightedProbMeasure hα hw_int hw_nonneg,
    integral_weightedProbMeasure hα hw_int hw_nonneg] at hjensen
  have hmax_pos : 0 < α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ := hδ.trans_le <| by
    rw [le_inv_mul_iff₀ hα, mul_comm α δ, ← hw_sum, ← integral_const_mul]
    exact integral_mono_ae (hw_int.const_mul δ) hmax_int
      (hw_nonneg.mono fun _ hs ↦ mul_le_mul_of_nonneg_right (le_max_right _ _) hs)
  have hf_int : Integrable (fun s ↦ ‖f s‖ * w s) μ := hw_int.bdd_mul
    (map_continuous f).norm.aestronglyMeasurable
    (ae_of_all _ fun s ↦ by rw [norm_norm]; exact norm_coe_le_norm f s)
  have hmax_le : α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ ≤ α⁻¹ * (∫ s, ‖f s‖ * w s ∂μ) + δ := by
    have hint : ∫ s, max ‖f s‖ δ * w s ∂μ ≤ (∫ s, ‖f s‖ * w s ∂μ) + δ * α :=
      (integral_mono_ae hmax_int (hf_int.add (hw_int.const_mul δ)) (hw_nonneg.mono fun s hs ↦ by
        rw [Pi.add_apply, ← add_mul]; exact mul_le_mul_of_nonneg_right (max_le
          (le_add_of_nonneg_right hδ.le) (le_add_of_nonneg_left (norm_nonneg _))) hs)).trans_eq
        (by simp only [Pi.add_apply]
            rw [integral_add hf_int (hw_int.const_mul δ), integral_const_mul, hw_sum])
    refine (mul_le_mul_of_nonneg_left hint (inv_pos.2 hα).le).trans_eq ?_
    rw [mul_add, mul_left_comm, inv_mul_cancel₀ hα.ne', mul_one]
  refine (Real.exp_le_exp.2 ((inv_mul_le_iff₀ hα).1 hjensen)).trans_eq ?_ |>.trans
    (Real.rpow_le_rpow hmax_pos.le hmax_le hα.le)
  rw [Real.rpow_def_of_pos hmax_pos, mul_comm α]

end ZeroAtInftyContinuousMap
