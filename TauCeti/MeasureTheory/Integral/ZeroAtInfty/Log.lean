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
import TauCeti.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Weighted logarithmic integrals of bounded continuous and `C₀` functions

For a threshold `δ > 0`, a bounded continuous function `f : Ω →ᵇ E`, and an almost everywhere
nonnegative integrable weight `w` of total mass `∫ w ∂μ = α > 0`, this file develops the
measure-theoretic properties of the clipped logarithmic envelope `TauCeti.logMaxDiv f δ`:

* `ZeroAtInftyContinuousMap.integrable_logMaxDiv`: when `f : C₀(Ω, E)`, `[R1Space Ω]`, and `μ`
  is finite on compact sets (`[IsFiniteMeasureOnCompacts μ]`), `TauCeti.logMaxDiv f δ` is
  `μ`-integrable;
* `BoundedContinuousFunction.integrable_logMaxDiv_mul`: `(TauCeti.logMaxDiv f δ ·) * w` is
  `μ`-integrable for any `μ`-integrable `w`;
* `BoundedContinuousFunction.integral_log_max_mul_eq`: the weighted splitting identity
  `∫ Real.log (max ‖f s‖ δ) * w s ∂μ =`
  `(∫ Real.log δ * w s ∂μ) + (∫ TauCeti.logMaxDiv f δ s * w s ∂μ)`;
* `BoundedContinuousFunction.exp_integral_log_max_le_rpow`: weighted logarithmic Jensen inequality
  `exp (∫ Real.log (max ‖f s‖ δ) * w s ∂μ) ≤ (α⁻¹ * ∫ ‖f s‖ * w s ∂μ + δ) ^ α`.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal ZeroAtInfty

namespace ZeroAtInftyContinuousMap

/-- For `f : C₀(Ω, E)`, `δ > 0`, and `[R1Space Ω]`, the clipped logarithmic envelope
`TauCeti.logMaxDiv f δ` is integrable with respect to any measure `μ` finite on compact sets. -/
theorem integrable_logMaxDiv {Ω E : Type*} [TopologicalSpace Ω] [R1Space Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasureOnCompacts μ]
    [SeminormedAddCommGroup E] (f : C₀(Ω, E)) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (TauCeti.logMaxDiv f δ) μ :=
  (TauCeti.continuous_logMaxDiv (map_continuous f) hδ).integrable_of_hasCompactSupport
    (hasCompactSupport_logMaxDiv f hδ)

end ZeroAtInftyContinuousMap

namespace BoundedContinuousFunction

/-- For `f : Ω →ᵇ E`, `δ > 0`, and an integrable weight `w`, `(TauCeti.logMaxDiv f δ ·) * w` is
integrable. -/
theorem integrable_logMaxDiv_mul {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : Ω →ᵇ E) {δ : ℝ}
    (hδ : 0 < δ) {w : Ω → ℝ} (hw_int : Integrable w μ) :
    Integrable (fun s ↦ TauCeti.logMaxDiv f δ s * w s) μ :=
  hw_int.bdd_mul (c := Real.log (max ‖f‖ δ / δ))
    (TauCeti.continuous_logMaxDiv f.continuous hδ).aestronglyMeasurable (ae_of_all _ fun s ↦ by
      rw [Real.norm_of_nonneg (TauCeti.logMaxDiv_nonneg f hδ s), TauCeti.logMaxDiv_def]
      exact Real.log_le_log (div_pos (hδ.trans_le (le_max_right _ _)) hδ)
        (div_le_div_of_nonneg_right (max_le_max (f.norm_coe_le_norm s) le_rfl) hδ.le))

/-- Splitting identity for a clipped weighted logarithmic integral of `f : Ω →ᵇ E` with threshold
`δ > 0` and integrable weight `w`:
`∫ Real.log (max ‖f s‖ δ) * w s ∂μ =`
`(∫ Real.log δ * w s ∂μ) + (∫ TauCeti.logMaxDiv f δ s * w s ∂μ)`. -/
theorem integral_log_max_mul_eq {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : Ω →ᵇ E) {δ : ℝ}
    (hδ : 0 < δ) {w : Ω → ℝ} (hw_int : Integrable w μ) : (∫ s, Real.log (max ‖f s‖ δ) * w s ∂μ) =
      (∫ s, Real.log δ * w s ∂μ) + (∫ s, TauCeti.logMaxDiv f δ s * w s ∂μ) := by
  rw [show (fun s ↦ Real.log (max ‖f s‖ δ) * w s) =
      fun s ↦ Real.log δ * w s + TauCeti.logMaxDiv f δ s * w s from
      funext fun s ↦ by rw [← add_mul, TauCeti.log_add_logMaxDiv f hδ],
    integral_add (hw_int.const_mul _) (f.integrable_logMaxDiv_mul hδ hw_int)]

/-- Normalize the finite measure `w · μ` to a probability measure and apply Jensen's inequality
for `Real.log` to `s ↦ max ‖f s‖ δ`. -/
private theorem inv_mul_integral_log_max_le {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : Ω →ᵇ E)
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
  have hnorm_meas : (ν.normalize : Measure Ω) = ν.mass⁻¹ • ν0 := by
    rw [← ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure,
      ν.normalize_eq_inv_mass_smul_of_ne_zero
        ((ν.mass_ne_zero_iff).1 (hν_mass ▸ NNReal.coe_ne_zero.1 hα.ne')),
      FiniteMeasure.toMeasure_smul, FiniteMeasure.toMeasure_mk]
  -- Translate integrability and integrals from `ν.normalize` back to `w`-weighted `μ`-integrals.
  have hint_norm {u : Ω → ℝ} (hu : Integrable (fun s ↦ u s * w s) μ) :
      Integrable u (ν.normalize : Measure Ω) := hnorm_meas ▸
    ((TauCeti.MeasureTheory.integrable_withDensity_ofReal_iff hw_int.aemeasurable hw_nonneg).2
      (hu.congr (ae_of_all _ fun _ ↦ mul_comm _ _))).smul_measure ENNReal.coe_ne_top
  have hintegral_norm (u : Ω → ℝ) :
      ∫ s, u s ∂(ν.normalize : Measure Ω) = α⁻¹ * ∫ s, u s * w s ∂μ := by
    rw [hnorm_meas, integral_smul_nnreal_measure, hν_mass,
      TauCeti.MeasureTheory.integral_withDensity_ofReal hw_int.aemeasurable hw_nonneg]
    simp only [α_nn, NNReal.smul_def, smul_eq_mul]
    exact congrArg (α⁻¹ * ·) (integral_congr_ae (ae_of_all _ fun _ ↦ mul_comm _ _))
  have hlog_int : Integrable (fun s ↦ Real.log (max ‖f s‖ δ) * w s) μ :=
    ((hw_int.const_mul (Real.log δ)).add (f.integrable_logMaxDiv_mul hδ hw_int)).congr
      (ae_of_all _ fun s ↦ by rw [Pi.add_apply, ← add_mul, TauCeti.log_add_logMaxDiv f hδ])
  rw [← hintegral_norm, ← hintegral_norm]
  exact (strictConcaveOn_log_Ioi.concaveOn.subset (Set.Ici_subset_Ioi.2 hδ)
    (convex_Ici δ)).le_map_integral (Real.continuousOn_log.mono fun _ hx ↦ (hδ.trans_le hx).ne')
    isClosed_Ici (ae_of_all _ fun _ ↦ le_max_right _ _) (hint_norm hmax_int) (hint_norm hlog_int)

/-- Weighted logarithmic mean bound for a clipped bounded continuous function `f : Ω →ᵇ E`: for a
threshold `δ > 0` and an almost everywhere nonnegative integrable weight `w` of total mass
`∫ w ∂μ = α > 0`, `exp (∫ Real.log (max ‖f s‖ δ) * w s ∂μ) ≤ (α⁻¹ * ∫ ‖f s‖ * w s ∂μ + δ) ^ α`. -/
theorem exp_integral_log_max_le_rpow {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : Ω →ᵇ E)
    {w : Ω → ℝ} {α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) (hw_int : Integrable w μ)
    (hw_nonneg : 0 ≤ᵐ[μ] w) (hw_sum : ∫ s, w s ∂μ = α) :
    Real.exp (∫ s, Real.log (max ‖f s‖ δ) * w s ∂μ) ≤ (α⁻¹ * (∫ s, ‖f s‖ * w s ∂μ) + δ) ^ α := by
  have hmax_int := f.integrable_max_norm_mul δ hw_int
  have hjensen := f.inv_mul_integral_log_max_le hα hδ hw_int hw_nonneg hw_sum hmax_int
  have hmax_pos : 0 < α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ := hδ.trans_le <| by
    rw [le_inv_mul_iff₀ hα, mul_comm α δ, ← hw_sum, ← integral_const_mul]
    exact integral_mono_ae (hw_int.const_mul δ) hmax_int
      (hw_nonneg.mono fun _ hs ↦ mul_le_mul_of_nonneg_right (le_max_right _ _) hs)
  refine ((Real.exp_le_exp.2 ((inv_mul_le_iff₀ hα).1 hjensen)).trans_eq
    (by rw [Real.rpow_def_of_pos hmax_pos, mul_comm α])).trans
    (Real.rpow_le_rpow hmax_pos.le (f.inv_mul_integral_max_le hδ.le hw_int hw_nonneg hw_sum) hα.le)

end BoundedContinuousFunction
