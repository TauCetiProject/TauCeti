/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# `Lᵖ` bounds for bounded functions supported in a set

A function bounded by `C` and supported in a set `s` has `eLpNorm f p μ ≤ μ s ^ (1/p) C`
(`MeasureTheory.eLpNorm_le_of_ae_bound_of_support_subset`). This sharpens Mathlib's
`MeasureTheory.eLpNorm_le_of_ae_bound`, which has the measure of the whole space in place of
`μ s`, and is the usual way to bound the `Lᵖ` norm of a compactly supported function. The same
bound for the norm of the class in `Lᵖ(μ)` is `MeasureTheory.MemLp.norm_toLp_le_of_support_subset`.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}

/-- A function bounded by `C` almost everywhere and supported in a set `s` has `Lᵖ` seminorm at
most `μ s ^ (1/p) C`. -/
theorem eLpNorm_le_of_ae_bound_of_support_subset {f : α → F} {s : Set α} {C : ℝ} {p : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hfs : Function.support f ⊆ s) (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    eLpNorm f p μ ≤ μ s ^ p.toReal⁻¹ * ENNReal.ofReal C := by
  rw [← eLpNorm_restrict_eq_of_support_subset hf hfs, ← Measure.restrict_apply_univ]
  exact eLpNorm_le_of_ae_bound hf.restrict (ae_restrict_of_ae hfC)

/-- The `Lᵖ(μ)` class of a function supported in a set `s` of finite measure and bounded by `C`
almost everywhere has norm at most `μ(s)^(1/p) C`. -/
theorem MemLp.norm_toLp_le_of_support_subset {f : α → F} {p : ℝ≥0∞} (hf : MemLp f p μ)
    {s : Set α} (hs : μ s ≠ ⊤) (hfs : Function.support f ⊆ s) {C : ℝ} (hC : 0 ≤ C)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    ‖hf.toLp f‖ ≤ (μ s ^ p.toReal⁻¹).toReal * C := by
  rw [Lp.norm_toLp, ← ENNReal.toReal_ofReal hC, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hs) ENNReal.ofReal_ne_top)
    (eLpNorm_le_of_ae_bound_of_support_subset hf.aestronglyMeasurable hfs hfC)

end MeasureTheory
