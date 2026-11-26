/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# Weighted norm truncation integrals of functions vanishing at infinity

For a continuous function `f : C₀(Ω, E)` vanishing at infinity, a threshold `δ : ℝ`, and an
integrable weight `w : Ω → ℝ`, this file records the basic integrability and upper-bound estimates
for the truncated norm `s ↦ max ‖f s‖ δ` against `w`:

* `ZeroAtInftyContinuousMap.integrable_max_norm_mul`: `s ↦ max ‖f s‖ δ * w s` is `μ`-integrable;
* `ZeroAtInftyContinuousMap.inv_mul_integral_max_le`: when `0 ≤ δ`, `0 ≤ᵐ[μ] w`, and
  `∫ s, w s ∂μ = α`, `α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ ≤ α⁻¹ * (∫ s, ‖f s‖ * w s ∂μ) + δ`.
-/

public section

namespace ZeroAtInftyContinuousMap

open MeasureTheory
open scoped ZeroAtInfty

/-- For `f : C₀(Ω, E)`, any threshold `δ : ℝ`, and an integrable weight `w`,
`s ↦ max ‖f s‖ δ * w s` is integrable. -/
theorem integrable_max_norm_mul {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : C₀(Ω, E)) (δ : ℝ)
    {w : Ω → ℝ} (hw_int : Integrable w μ) :
    Integrable (fun s ↦ max ‖f s‖ δ * w s) μ :=
  hw_int.bdd_mul ((map_continuous f).norm.max continuous_const).aestronglyMeasurable
    (ae_of_all _ fun s ↦ by
      rw [Real.norm_of_nonneg ((norm_nonneg _).trans (le_max_left _ _))]
      exact max_le_max (norm_coe_le_norm f s) le_rfl)

/-- For `f : C₀(Ω, E)`, threshold `δ ≥ 0`, and an almost everywhere nonnegative integrable weight
`w` of total mass `∫ s, w s ∂μ = α`,
`α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ ≤ α⁻¹ * (∫ s, ‖f s‖ * w s ∂μ) + δ`. -/
theorem inv_mul_integral_max_le {Ω E : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [SeminormedAddCommGroup E] (f : C₀(Ω, E))
    {w : Ω → ℝ} {α δ : ℝ} (hδ : 0 ≤ δ) (hw_int : Integrable w μ)
    (hw_nonneg : 0 ≤ᵐ[μ] w) (hw_sum : ∫ s, w s ∂μ = α) :
    α⁻¹ * ∫ s, max ‖f s‖ δ * w s ∂μ ≤ α⁻¹ * (∫ s, ‖f s‖ * w s ∂μ) + δ := by
  rcases eq_or_lt_of_le (hw_sum ▸ integral_nonneg_of_ae hw_nonneg) with rfl | hα
  · simpa using hδ
  · have hmax_int : Integrable (fun s ↦ max ‖f s‖ δ * w s) μ := integrable_max_norm_mul f δ hw_int
    have hf_int : Integrable (fun s ↦ ‖f s‖ * w s) μ := hw_int.bdd_mul
      (map_continuous f).norm.aestronglyMeasurable
      (ae_of_all _ fun s ↦ by rw [norm_norm]; exact norm_coe_le_norm f s)
    have hint : ∫ s, max ‖f s‖ δ * w s ∂μ ≤ (∫ s, ‖f s‖ * w s ∂μ) + δ * α :=
      (integral_mono_ae hmax_int (hf_int.add (hw_int.const_mul δ)) (hw_nonneg.mono fun s hs ↦ by
        rw [Pi.add_apply, ← add_mul]; exact mul_le_mul_of_nonneg_right (max_le
          (le_add_of_nonneg_right hδ) (le_add_of_nonneg_left (norm_nonneg _))) hs)).trans_eq
        (by simp only [Pi.add_apply, integral_add hf_int (hw_int.const_mul δ), integral_const_mul,
          hw_sum])
    refine (mul_le_mul_of_nonneg_left hint (inv_pos.2 hα).le).trans_eq ?_
    rw [mul_add, mul_left_comm, inv_mul_cancel₀ hα.ne', mul_one]

end ZeroAtInftyContinuousMap
