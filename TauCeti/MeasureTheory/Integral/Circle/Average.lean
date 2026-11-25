/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Circle averages over the polar angles and their local radial continuity

`TauCeti.circleAverage_eq_integral_neg_pi_pi` writes `Real.circleAverage f c R` as the normalized
integral over the angles `[-π, π]`, the angular range of the polar-coordinate formulas such as
`TauCeti.integral_annulus_eq_integral_circleMap`, rather than over `[0, 2π]` as in its definition.

Mathlib's `Continuous.circleAverage` and `ContinuousOn.circleAverage` establish continuity of
`Real.circleAverage f c` globally when `f` is continuous on `ℂ`, or on a set of nonnegative radii
over whose concentric circles `f` is continuous. When `f` has interior singularities inside
`ball c |R|`, global continuity fails, yet if `f` is continuous on any neighbourhood of
`sphere c |R|`, thickening `sphere c |R|` into an open annulus and using radius-sign invariance
(`Real.circleAverage_abs_radius`) gives continuity of `Real.circleAverage f c` at `R` (including at
`R = 0` and at negative radii).
-/

public section

open Metric Real Set Topology

namespace TauCeti

/-- The circle average is the normalized integral over the angles `[-π, π]`, the angular range of
the polar-coordinate formulas, instead of the period `[0, 2π]` of its definition. -/
theorem circleAverage_eq_integral_neg_pi_pi {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℂ → E} {c : ℂ} {R : ℝ} :
    circleAverage f c R = (2 * π)⁻¹ • ∫ θ in -π..π, f (circleMap c R θ) := by
  rw [circleAverage_eq_integral_add (-π),
    intervalIntegral.integral_comp_add_right (fun θ ↦ f (circleMap c R θ)), zero_add, two_mul,
    add_neg_cancel_right]

end TauCeti

/-- If `f : ℂ → E` is continuous on a set `s` that is a neighbourhood of `sphere c |R|`, then
`Real.circleAverage f c` is continuous at `R` (including when `f` has singularities inside
`ball c |R|` or when `R ≤ 0`). -/
theorem ContinuousOn.continuousAt_circleAverage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℂ → E} {s : Set ℂ} {c : ℂ} {R : ℝ} (hf : ContinuousOn f s)
    (hs : s ∈ 𝓝ˢ (sphere c |R|)) : ContinuousAt (Real.circleAverage f c) R := by
  obtain ⟨δ, hδ, hsub⟩ := (Metric.mem_nhdsSet_iff (isCompact_sphere c |R|)).mp hs
  set I : Set ℝ := {r : ℝ | 0 ≤ r ∧ dist r |R| < δ}
  have hann : {z : ℂ | ‖z - c‖ ∈ I} ⊆ s := by
    intro z hz
    simp only [I, mem_ofPred_eq, norm_nonneg, true_and] at hz
    refine hsub (mem_thickening_iff.mpr ?_)
    rcases eq_or_ne (z - c) 0 with hzc | hzc
    · refine ⟨c + R, by simp, ?_⟩
      rw [sub_eq_zero.mp hzc]
      simpa [hzc, Real.dist_eq] using hz
    · refine ⟨c + (|R| / ‖z - c‖ : ℝ) • (z - c), ?_, ?_⟩
      · rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_smul,
          Real.norm_of_nonneg (div_nonneg (abs_nonneg R) (norm_nonneg _)),
          div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hzc)]
      · have hdiff : z - (c + (|R| / ‖z - c‖ : ℝ) • (z - c)) =
            ((‖z - c‖ - |R|) / ‖z - c‖ : ℝ) • (z - c) := by
          rw [sub_add_eq_sub_sub, sub_div, div_self (norm_ne_zero_iff.mpr hzc), sub_smul, one_smul]
        rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_div,
          abs_of_pos (norm_pos_iff.mpr hzc), div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hzc),
          ← Real.dist_eq]
        exact hz
  have hcont_I : ContinuousOn (Real.circleAverage f c) I :=
    ContinuousOn.circleAverage (hf.mono hann) fun _ hr ↦ hr.1
  set U : Set ℝ := {r : ℝ | dist |r| |R| < δ}
  have hU_open : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hcont_U : ContinuousOn (Real.circleAverage f c) U :=
    (hcont_I.comp continuous_abs.continuousOn fun r hr ↦ ⟨abs_nonneg r, hr⟩).congr
      fun r _ ↦ by simp
  exact hcont_U.continuousAt (hU_open.mem_nhds (by simp [U, hδ]))

-- `z ↦ z⁻¹` has an interior pole at `0`, yet `circleAverage (·⁻¹) 0` is continuous at `R = 1`.
example : ContinuousAt (Real.circleAverage (fun z : ℂ ↦ z⁻¹) 0) 1 := by
  have hs : ({0}ᶜ : Set ℂ) ∈ 𝓝ˢ (sphere (0 : ℂ) |1|) :=
    isOpen_compl_singleton.mem_nhdsSet.mpr fun z hz ↦ by
      rw [mem_compl_singleton_iff]
      rintro rfl
      simp at hz
  exact continuousOn_inv₀.continuousAt_circleAverage hs
