/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Log
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity
import TauCeti.MeasureTheory.Integral.ZeroAtInfty.Basic

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
open scoped ENNReal NNReal ZeroAtInfty

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

/-- Normalize the finite measure `w · μ` to a probability measure and apply Jensen's inequality
for `Real.log` to `s ↦ max ‖f s‖ δ`. -/
private theorem inv_mul_integral_log_max_le {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : C₀(Ω, E))
    {w : Ω → ℝ} {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hw_int : Integrable w μ)
    (hw_nonneg : 0 ≤ᵐ[μ] w) (hw_sum : ∫ s, w s ∂μ = α)
    (hmax_int : Integrable (fun s ↦ max ‖f s‖ δ * w s) μ) :
    α⁻¹ * ∫ s, Real.log (max ‖f s‖ δ) * w s ∂μ ≤ Real.log (α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ) := by
  -- Positive total mass forces `Ω` to be nonempty so `ν.normalize` is defined.
  have _ : Nonempty Ω := by_contra fun h ↦
    have _ := not_nonempty_iff.1 h; hα.ne' (hw_sum.symm.trans integral_of_isEmpty)
  let ν0 : Measure Ω := μ.withDensity (fun s ↦ ENNReal.ofReal (w s))
  have hν0_univ : ν0 Set.univ = ENNReal.ofReal α := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hw_int hw_nonneg, hw_sum]
  let ν : FiniteMeasure Ω := ⟨ν0, ⟨hν0_univ ▸ ENNReal.ofReal_lt_top⟩⟩
  let α_nn : ℝ≥0 := ⟨α, hα.le⟩
  have hν_mass : ν.mass = α_nn := ENNReal.coe_injective <|
    FiniteMeasure.ennreal_mass.trans (hν0_univ.trans (ENNReal.ofReal_eq_coe_nnreal hα.le))
  have hν_ne : ν ≠ 0 :=
    (ν.mass_ne_zero_iff).1 (hν_mass ▸ NNReal.coe_ne_zero.1 hα.ne')
  have hnorm_meas : (ν.normalize : Measure Ω) = ν.mass⁻¹ • ν0 := by
    rw [← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
      ν.normalize_eq_inv_mass_smul_of_ne_zero hν_ne, FiniteMeasure.toMeasure_smul,
      FiniteMeasure.toMeasure_mk]
  -- Translate integrability and integrals from `ν.normalize` back to `w`-weighted `μ`-integrals.
  have hint_norm {u : Ω → ℝ} (hu : Integrable (fun s ↦ u s * w s) μ) :
      Integrable u (ν.normalize : Measure Ω) := by
    rw [hnorm_meas]
    exact ((TauCeti.MeasureTheory.integrable_withDensity_ofReal_iff
      hw_int.aemeasurable hw_nonneg).2
      (hu.congr (ae_of_all _ fun _ ↦ mul_comm _ _))).smul_measure ENNReal.coe_ne_top
  have hintegral_norm (u : Ω → ℝ) :
      ∫ s, u s ∂(ν.normalize : Measure Ω) = α⁻¹ * ∫ s, u s * w s ∂μ := by
    rw [hnorm_meas, integral_smul_nnreal_measure, hν_mass,
      TauCeti.MeasureTheory.integral_withDensity_ofReal hw_int.aemeasurable hw_nonneg]
    simp only [α_nn, NNReal.smul_def, smul_eq_mul]
    exact congrArg (α⁻¹ * ·) (integral_congr_ae (ae_of_all _ fun _ ↦ mul_comm _ _))
  have hlog_int : Integrable (fun s ↦ Real.log (max ‖f s‖ δ) * w s) μ :=
    (log_max_mul_eq_add f hδ w).symm ▸
      (hw_int.const_mul _).add (integrable_logMaxDiv_mul f hδ hw_int)
  rw [← hintegral_norm, ← hintegral_norm]
  exact (strictConcaveOn_log_Ioi.concaveOn.subset (Set.Ici_subset_Ioi.2 hδ)
    (convex_Ici δ)).le_map_integral (Real.continuousOn_log.mono fun _ hx ↦ (hδ.trans_le hx).ne')
    isClosed_Ici (ae_of_all _ fun _ ↦ le_max_right _ _)
    (hint_norm hmax_int) (hint_norm hlog_int)

/-- Weighted logarithmic mean bound for a clipped `C₀(Ω, E)` function: for a threshold `δ > 0`
and an almost everywhere nonnegative integrable weight `w` of total mass `∫ w ∂μ = α > 0`,
`exp (∫ Real.log (max ‖f s‖ δ) * w s ∂μ) ≤ (α⁻¹ * ∫ ‖f s‖ * w s ∂μ + δ) ^ α`. -/
theorem exp_integral_log_max_le_rpow {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : C₀(Ω, E))
    {w : Ω → ℝ} {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hw_int : Integrable w μ)
    (hw_nonneg : 0 ≤ᵐ[μ] w) (hw_sum : ∫ s, w s ∂μ = α) :
    Real.exp (∫ s, Real.log (max ‖f s‖ δ) * w s ∂μ) ≤ (α⁻¹ * (∫ s, ‖f s‖ * w s ∂μ) + δ) ^ α := by
  have hmax_int := integrable_max_norm_mul f δ hw_int
  -- Apply Jensen to `log (max ‖f‖ δ)`, exponentiate, and bound `max ‖f‖ δ ≤ ‖f‖ + δ`.
  have hjensen := inv_mul_integral_log_max_le f hα hδ hw_int hw_nonneg hw_sum hmax_int
  have hmax_pos : 0 < α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ := hδ.trans_le <| by
    rw [le_inv_mul_iff₀ hα, mul_comm α δ, ← hw_sum, ← integral_const_mul]
    exact integral_mono_ae (hw_int.const_mul δ) hmax_int
      (hw_nonneg.mono fun _ hs ↦ mul_le_mul_of_nonneg_right (le_max_right _ _) hs)
  have hmax_le := inv_mul_integral_max_le f hδ.le hw_int hw_nonneg hw_sum
  refine (Real.exp_le_exp.2 ((inv_mul_le_iff₀ hα).1 hjensen)).trans_eq ?_ |>.trans
    (Real.rpow_le_rpow hmax_pos.le hmax_le hα.le)
  rw [Real.rpow_def_of_pos hmax_pos, mul_comm α]

end ZeroAtInftyContinuousMap
