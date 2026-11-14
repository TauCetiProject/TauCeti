/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Local radial continuity of the Nevanlinna proximity function

Mathlib's `ValueDistribution.continuous_proximity_top` establishes global continuity of
`ValueDistribution.proximity g ⊤` when `g : ℂ → E` is continuous on all of `ℂ`. When `g` is merely
meromorphic (or defined locally), interior poles prevent global continuity of `g`, yet at any radius
`R` whose circle `sphere 0 |R|` avoids the singularities of `g`, `g` is continuous on a
neighbourhood of `sphere 0 |R|` and `ValueDistribution.proximity g ⊤` is still continuous at `R`
(including across boundary zeros of `g`).
-/

public section

open Filter Metric Real Set Topology

/-- If `g : ℂ → E` is continuous on a set `s` that is a neighbourhood of `sphere 0 |R|`, then its
Nevanlinna proximity function `ValueDistribution.proximity g ⊤` is continuous at `R` (including
when `g` has poles inside `ball 0 |R|` or zeros on `sphere 0 |R|`). -/
theorem ContinuousOn.continuousAt_proximity_top {E : Type*} [NormedAddCommGroup E]
    {g : ℂ → E} {s : Set ℂ} {R : ℝ} (hg : ContinuousOn g s) (hs : s ∈ 𝓝ˢ (sphere 0 |R|)) :
    ContinuousAt (ValueDistribution.proximity g ⊤) R := by
  obtain ⟨δ, hδ, hsub⟩ := (Metric.mem_nhdsSet_iff (isCompact_sphere (0 : ℂ) |R|)).mp hs
  set I : Set ℝ := {r : ℝ | 0 ≤ r ∧ dist r |R| < δ}
  have hann : {z : ℂ | ‖z - 0‖ ∈ I} ⊆ s := by
    intro z hz
    simp only [I, mem_ofPred_eq, sub_zero, norm_nonneg, true_and] at hz
    refine hsub (mem_thickening_iff.mpr ?_)
    rcases eq_or_ne z 0 with rfl | hz0
    · refine ⟨(R : ℂ), by simp, ?_⟩
      simpa [dist_zero_left, Real.dist_eq] using hz
    · refine ⟨(|R| / ‖z‖ : ℝ) • z, ?_, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul,
          Real.norm_of_nonneg (div_nonneg (abs_nonneg R) (norm_nonneg z)),
          div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz0)]
      · have hdiff : z - (|R| / ‖z‖ : ℝ) • z = ((‖z‖ - |R|) / ‖z‖ : ℝ) • z := by
          rw [sub_div, div_self (norm_ne_zero_iff.mpr hz0), sub_smul, one_smul]
        rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_div,
          abs_of_pos (norm_pos_iff.mpr hz0), div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz0),
          ← Real.dist_eq]
        exact hz
  have hcont_I : ContinuousOn (ValueDistribution.proximity g ⊤) I := by
    rw [ValueDistribution.proximity_top]
    exact ContinuousOn.circleAverage
      (continuous_posLog.comp_continuousOn (hg.mono hann).norm) fun _ hr ↦ hr.1
  have heven :
      ∀ r : ℝ, ValueDistribution.proximity g ⊤ |r| = ValueDistribution.proximity g ⊤ r := by
    intro r
    rcases le_or_gt 0 r with hr | hr
    · rw [abs_of_nonneg hr]
    · rw [abs_of_neg hr, ValueDistribution.proximity_even r]
  set U : Set ℝ := {r : ℝ | dist |r| |R| < δ}
  have hU_open : IsOpen U := isOpen_lt (by fun_prop) continuous_const
  have hcont_U : ContinuousOn (ValueDistribution.proximity g ⊤) U :=
    (hcont_I.comp continuous_abs.continuousOn fun r hr ↦ ⟨abs_nonneg r, hr⟩).congr
      fun r _ ↦ (heven r).symm
  exact hcont_U.continuousAt (hU_open.mem_nhds (by simp [U, hδ]))

-- `z ↦ z⁻¹` has an interior pole at `0`, yet `proximity (·⁻¹) ⊤` is continuous at `R = 1`.
example : ContinuousAt (ValueDistribution.proximity (fun z : ℂ ↦ z⁻¹) ⊤) 1 := by
  have hs : ({0}ᶜ : Set ℂ) ∈ 𝓝ˢ (sphere (0 : ℂ) |1|) :=
    isOpen_compl_singleton.mem_nhdsSet.mpr fun z hz ↦ by
      rw [mem_compl_singleton_iff]
      rintro rfl
      simp at hz
  exact continuousOn_inv₀.continuousAt_proximity_top hs
