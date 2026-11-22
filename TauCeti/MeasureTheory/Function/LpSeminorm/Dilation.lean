/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Dilations of the real line and the `Lᵖ` seminorm

For `c ≠ 0`, the dilation `t ↦ c t` pushes Lebesgue measure on `ℝ` forward to `|c⁻¹|` times
Lebesgue measure (`Real.map_volume_mul_left`). Hence the `Lᵖ` seminorm of a dilate is

`‖f (c ·)‖_p = |c|^(-1/p) ‖f‖_p`

(`MeasureTheory.eLpNorm_comp_mul_left`), and dilations preserve almost everywhere strong
measurability (`MeasureTheory.AEStronglyMeasurable.comp_mul_left`). These are the time rescalings
of mixed-norm estimates such as the Strichartz estimates, where a family of operators `U(t)` is
replaced by `U(c t)`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] {c : ℝ}

/-- **The `Lᵖ` seminorm of a dilate.** For `c ≠ 0`, `‖f (c ·)‖_p = |c⁻¹|^(1/p) ‖f‖_p` on `ℝ`. -/
theorem eLpNorm_comp_mul_left (hc : c ≠ 0) (f : ℝ → ε) (p : ℝ≥0∞) :
    eLpNorm (fun t ↦ f (c * t)) p volume =
      ENNReal.ofReal |c⁻¹| ^ (1 / p).toReal * eLpNorm f p volume := by
  rw [← smul_eq_mul, ← eLpNorm_smul_measure_of_ne_zero (by simpa using hc),
    ← Real.map_volume_mul_left hc, (measurableEmbedding_mulLeft₀ hc).eLpNorm_map_measure]
  rfl

/-- Dilations of the real line preserve almost everywhere strong measurability. -/
theorem AEStronglyMeasurable.comp_mul_left {β : Type*} [TopologicalSpace β] {f : ℝ → β}
    (hf : AEStronglyMeasurable f) (hc : c ≠ 0) : AEStronglyMeasurable fun t ↦ f (c * t) := by
  refine (measurableEmbedding_mulLeft₀ hc).aestronglyMeasurable_map_iff.1 ?_
  rw [Real.map_volume_mul_left hc]
  exact hf.smul_measure _

end MeasureTheory
