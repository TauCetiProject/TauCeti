/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Continuity of squared norms from L² to L¹

The squared pointwise norms of L²-convergent functions converge in L¹, not just after
integration. The quantitative bound factors the difference of squares and applies Hölder.
It is useful when the squares are subsequently integrated over varying sets, as with
quadratic-energy clocks of stochastic integrands. No finiteness of the measure is required.
-/

public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α} {f g : α → E}

/-- The L¹ distance between squared norms is controlled by the L² distance times the sum
of the L² norms. -/
theorem eLpNorm_norm_sq_sub_le :
    eLpNorm (fun x ↦ ‖f x‖ ^ 2 - ‖g x‖ ^ 2) 1 μ ≤
      eLpNorm (f - g) 2 μ * (eLpNorm f 2 μ + eLpNorm g 2 μ) := by
  by_cases hfg : eLpNorm (f - g) 2 μ = 0
  · have heq := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).1 hfg
    rw [eLpNorm_eq_zero_of_ae_zero (p := 1) (f := fun x ↦ ‖f x‖ ^ 2 - ‖g x‖ ^ 2) ?_]
    · exact zero_le
    filter_upwards [heq] with x hx
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hx ⊢
    rw [hx]
  by_cases! hf : ¬ AEStronglyMeasurable f μ
  · simp [eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top hfg]
  by_cases! hg : ¬ AEStronglyMeasurable g μ
  · simp [eLpNorm_of_not_aestronglyMeasurable hg, ENNReal.mul_top hfg]
  have hpoint (x : α) : ‖‖f x‖ ^ 2 - ‖g x‖ ^ 2‖ ≤
      ‖‖f x - g x‖ * (‖f x‖ + ‖g x‖)‖ := by
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))), Real.norm_eq_abs, sq_sub_sq, abs_mul,
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le _ _) (by positivity)
  calc
    _ ≤ eLpNorm (fun x ↦ ‖f x - g x‖ * (‖f x‖ + ‖g x‖)) 1 μ :=
      eLpNorm_mono_ae
        ((hf.norm.pow 2).sub (hg.norm.pow 2))
        (.of_forall hpoint)
    _ ≤ eLpNorm (fun x ↦ ‖f x - g x‖) 2 μ *
        eLpNorm (fun x ↦ ‖f x‖ + ‖g x‖) 2 μ := by
      simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def, Pi.add_def, Pi.sub_apply] using
        (eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
          (hf.sub hg).norm (hf.norm.add hg.norm))
    _ ≤ _ := by
      simp_rw [← Pi.sub_apply]
      rw [eLpNorm_norm _ (hf.sub hg)]
      gcongr
      simpa only [Pi.add_def, eLpNorm_norm _ hf, eLpNorm_norm _ hg] using
        (eLpNorm_add_le (f := fun x ↦ ‖f x‖) (g := fun x ↦ ‖g x‖)
          (μ := μ) (by norm_num : (1 : ℝ≥0∞) ≤ 2))

/-- L² convergence implies L¹ convergence of squared pointwise norms, for any measure
and any normed additive commutative group of values. -/
theorem tendsto_eLpNorm_norm_sq_sub {F : ι → α → E} {l : Filter ι}
    (hf : MemLp f 2 μ) (hlim : Tendsto (fun i ↦ eLpNorm (F i - f) 2 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (fun x ↦ ‖F i x‖ ^ 2 - ‖f x‖ ^ 2) 1 μ) l (𝓝 0) := by
  have hn : Tendsto (fun i ↦ eLpNorm (F i - f) 2 μ + eLpNorm f 2 μ + eLpNorm f 2 μ)
      l (𝓝 (eLpNorm f 2 μ + eLpNorm f 2 μ)) := by
    simpa only [zero_add] using (hlim.add_const (eLpNorm f 2 μ)).add_const (eLpNorm f 2 μ)
  have hb := ENNReal.Tendsto.mul hlim
    (Or.inr (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hf.eLpNorm_ne_top⟩))
    hn (Or.inr (by simp))
  simp only [zero_mul] at hb
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (.of_forall fun _ ↦ zero_le) (.of_forall fun i ↦ eLpNorm_norm_sq_sub_le.trans ?_)
  have hFi : eLpNorm (F i) 2 μ ≤ eLpNorm (F i - f) 2 μ + eLpNorm f 2 μ := by
    simpa only [sub_add_cancel] using
      (eLpNorm_add_le (f := F i - f) (g := f) (μ := μ) (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  gcongr

end MeasureTheory
