/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Norm

import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

omit [CompleteSpace E] [BorelSpace E] in
private theorem tendsto_toLp_centeredTruncation
    (h₂ : MemLp (id : E → E) 2 μ) (hmean : ∫ x, x ∂μ = 0) :
    Tendsto (fun R : ℝ≥0 ↦ (h₂.aestronglyMeasurable.memLp_centeredTruncation (p := 2) R).toLp
      (centeredTruncation id μ R)) atTop (𝓝 (h₂.toLp id)) := by
  let T (R : ℝ) (x : E) := if ‖x‖ ≤ R then x else 0
  let m (R : ℝ) := ∫ x, T R x ∂μ
  have hT (R : ℝ) : MemLp (T R) 2 μ := h₂.ite_norm_le R
  have hTout : Tendsto (fun R ↦ (hT R).toLp (T R)) atTop (𝓝 (h₂.toLp id)) := by
    have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    refine tendsto_toLp_of_ae_tendsto_of_norm_le (by norm_num) hT h₂.coeFn_toLp
      (fun R ↦ .of_forall fun x ↦ ?_) (.of_forall fun x ↦ ?_)
    · dsimp only [T, id_eq]
      split_ifs <;> simp
    · exact tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop ‖x‖] with R hR
        simp [T, hR])
  have hm : Tendsto m atTop (𝓝 0) :=
    hmean ▸ (h₂.integrable (by norm_num)).tendsto_integral_ite_norm_le
  have hconst := ((Lp.constL 2 μ ℝ : E →L[ℝ] Lp E 2 μ).continuous.tendsto 0).comp hm
  have hCenter : Tendsto (fun R ↦ (hT R).toLp (T R) - Lp.const 2 μ (m R))
      atTop (𝓝 (h₂.toLp id)) := by
    simpa only [Lp.constL_apply, Function.comp_def, map_zero, sub_zero] using hTout.sub hconst
  refine (hCenter.comp (NNReal.tendsto_coe_atTop.mpr tendsto_id)).congr fun R ↦ ?_
  have hC : centeredTruncation id μ R = T R - fun _ ↦ m R := by
    simp only [centeredTruncation_def, T, m, Set.indicator_apply, Set.mem_ofPred_eq, id_eq,
      Pi.sub_def]
  rw [Function.comp_apply, ← MemLp.toLp_const, ← MemLp.toLp_sub]
  exact MemLp.toLp_congr _ _ (.of_forall fun x ↦ congrFun hC.symm x)

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
  let C := centeredTruncation id μ
  have hC (R : ℝ≥0) : MemLp (C R) 2 μ := h₂.aestronglyMeasurable.memLp_centeredTruncation R
  have hCenter := tendsto_toLp_centeredTruncation h₂ hmean
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
  have hUlim : Tendsto (fun R ↦ (hU R).toLp (U R)) atTop (𝓝 (h₂.toLp id)) := by
    simp_rw [hULp]
    simpa only [C, inv_one, one_smul] using (hs.inv₀ one_ne_zero).smul hCenter
  have hr : Tendsto (fun k : ℕ ↦ (k : ℝ≥0) + R₀) atTop atTop :=
    tendsto_atTop_mono (fun _ ↦ le_self_add) tendsto_natCast_atTop_atTop
  refine ⟨fun k ↦ U ((k : ℝ≥0) + R₀), fun k ↦ ?_, ?_⟩
  · set R := (k : ℝ≥0) + R₀
    have hspos : 0 < s R := hR₀ R le_add_self
    have hbound (x : E) : ‖U R x‖ ≤ (s R)⁻¹ * (2 * R) := by
      simpa only [U, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hspos.le)]
        using mul_le_mul_of_nonneg_left (norm_centeredTruncation_le (X := id) (P := μ) R x)
          (inv_nonneg.mpr hspos.le)
    have hcenter : (∫ x, U R x ∂μ) = 0 := by
      simp only [U, C, Pi.smul_apply, integral_smul,
        h₂.aestronglyMeasurable.integral_centeredTruncation, smul_zero]
    refine ⟨(continuous_const_smul _).measurable.comp (measurable_id.centeredTruncation R),
      ⟨_, hbound⟩, hcenter, ?_⟩
    have hnormC : ‖(hC R).toLp (C R)‖ = s R := rfl
    rw [← (hU R).norm_toLp_sq, hULp, norm_smul,
      Real.norm_of_nonneg (by positivity), hnormC, inv_mul_cancel₀ hspos.ne', one_pow]
  · have hdiff := ((tendsto_const_nhds (x := h₂.toLp id)).sub (hUlim.comp hr)).norm.pow 2
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hdiff
    simpa only [Function.comp_def, ← MemLp.toLp_sub, MemLp.norm_toLp_sq, Pi.sub_apply, id_eq]
      using hdiff

end TauCeti.Probability
