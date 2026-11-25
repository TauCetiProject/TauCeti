/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Norm

import TauCeti.Probability.Moments.CenteredTruncation

/-!
# Bounded approximation preserving the first two moments

A centered real or complex entry of unit second absolute moment can be approximated in
mean square by bounded measurable functions of the entry. Cutting off at a large radius,
subtracting the new mean, and dividing by the new root mean square preserves the
normalization needed in limits for standardized random matrices.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- A centered law with unit second absolute moment admits bounded, centered, unit second
moment approximations obtained by measurable maps of the original variable. The errors
converge to zero in mean square. The `MemLp` hypothesis includes almost-everywhere strong
measurability of the identity. -/
theorem exists_bounded_centered_unitSecondMoment_approx
    (h₂ : MemLp (id : E → E) 2 μ) (hmean : ∫ x, x ∂μ = 0)
    (hunit : ∫ x, ‖x‖ ^ 2 ∂μ = 1) :
    ∃ f : ℕ → E → E,
      (∀ k, Measurable (f k) ∧ (∃ B : ℝ, ∀ x, ‖f k x‖ ≤ B) ∧
        (∫ x, f k x ∂μ) = 0 ∧ ∫ x, ‖f k x‖ ^ 2 ∂μ = 1) ∧
      Tendsto (fun k ↦ ∫ x, ‖x - f k x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  let C (R : ℝ≥0) : E → E := centeredTruncation id μ R
  have hC (R : ℝ≥0) : MemLp (C R) 2 μ := h₂.aestronglyMeasurable.memLp_centeredTruncation R
  have hCenter : Tendsto (fun R : ℝ≥0 ↦ (hC R).toLp (C R)) atTop (𝓝 (h₂.toLp id)) := by
    convert h₂.tendsto_toLp_centeredTruncation using 2
    exact MemLp.toLp_congr _ _ (.of_forall fun x ↦ by simp only [id_eq, hmean, sub_zero])
  let s (R : ℝ≥0) := ‖(hC R).toLp (C R)‖
  have hnorm : ‖h₂.toLp id‖ = 1 := by
    have hs := h₂.norm_toLp_sq
    simp only [id_eq, hunit] at hs
    nlinarith [norm_nonneg (h₂.toLp id)]
  have hs : Tendsto s atTop (𝓝 1) := hnorm ▸ hCenter.norm
  -- Normalization is well defined once the L² norms are positive.
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 ((tendsto_order.1 hs).1 0 zero_lt_one)
  let U (R : ℝ≥0) : E → E := (s R)⁻¹ • C R
  have hU (R : ℝ≥0) : MemLp (U R) 2 μ := (hC R).const_smul _
  have hULp (R : ℝ≥0) : (hU R).toLp (U R) = (s R)⁻¹ • (hC R).toLp (C R) :=
    MemLp.toLp_const_smul _ (hC R)
  have hUlim : Tendsto (fun R : ℝ≥0 ↦ (hU R).toLp (U R)) atTop (𝓝 (h₂.toLp id)) := by
    simp_rw [hULp]
    simpa only [inv_one, one_smul] using (hs.inv₀ one_ne_zero).smul hCenter
  have hr : Tendsto (fun k : ℕ ↦ (k : ℝ≥0) + R₀) atTop atTop :=
    tendsto_atTop_mono (fun _ ↦ le_self_add)
      (NNReal.tendsto_coe_atTop.mp (by simpa only [NNReal.coe_natCast] using
        tendsto_natCast_atTop_atTop))
  refine ⟨fun k ↦ U ((k : ℝ≥0) + R₀), fun k ↦ ?_, ?_⟩
  · set R : ℝ≥0 := (k : ℝ≥0) + R₀
    have hspos : 0 < s R := hR₀ R (le_add_of_nonneg_left (Nat.cast_nonneg k))
    have hbound (x : E) : ‖U R x‖ ≤ (s R)⁻¹ * (2 * (R : ℝ)) := by
      simpa only [U, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hspos.le)]
        using mul_le_mul_of_nonneg_left (norm_centeredTruncation_le R x)
          (inv_nonneg.mpr hspos.le)
    have hcenter : (∫ x, U R x ∂μ) = 0 := by
      simp only [U, C, Pi.smul_apply, integral_smul,
        h₂.aestronglyMeasurable.integral_centeredTruncation R, smul_zero]
    refine ⟨(continuous_const_smul _).measurable.comp (measurable_id.centeredTruncation R),
      ⟨_, hbound⟩, hcenter, ?_⟩
    rw [← (hU R).norm_toLp_sq, hULp, norm_smul,
      Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hspos.ne', one_pow]
  · have hdiff := ((tendsto_const_nhds (x := h₂.toLp id)).sub (hUlim.comp hr)).norm.pow 2
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hdiff
    simpa only [Function.comp_def, ← MemLp.toLp_sub, MemLp.norm_toLp_sq, Pi.sub_apply, id_eq]
      using hdiff

end TauCeti.Probability
