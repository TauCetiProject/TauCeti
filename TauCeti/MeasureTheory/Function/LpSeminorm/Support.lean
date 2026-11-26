/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# `Lᵖ` norms of functions supported in a set

A function bounded by `C` and supported in a set `s` has `eLpNorm f p μ ≤ μ s ^ (1/p) C`
(`MeasureTheory.eLpNorm_le_of_ae_bound_of_support_subset`). This sharpens Mathlib's
`MeasureTheory.eLpNorm_le_of_ae_bound`, which has the measure of the whole space in place of
`μ s`, and is the usual way to bound the `Lᵖ` norm of a compactly supported function. The same
bound for the real-valued norm `MeasureTheory.lpNorm`, when `μ s` is finite, is
`MeasureTheory.lpNorm_le_of_ae_bound_of_support_subset`, and for the norm of the class in `Lᵖ(μ)`
it is `MeasureTheory.MemLp.norm_toLp_le_of_support_subset`.

A function vanishing almost everywhere outside a set `s` has the same `Lᵖ` norm for `μ` and for
`μ.restrict s` (`MeasureTheory.eLpNorm_restrict_eq_of_ae_compl_eq_zero`), the almost-everywhere
version of Mathlib's `MeasureTheory.eLpNorm_restrict_eq_of_support_subset`. For classes in `Lᵖ`
this says that restricting an element of `Lᵖ(μ|t)` vanishing off `s ⊆ t` to `Lᵖ(μ|s)` preserves
its norm (`MeasureTheory.Lp.norm_eq_norm_of_ae_eq_restrict`).
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

/-- A function bounded by `C ≥ 0` almost everywhere and supported in a set `s` of finite measure
has real `Lᵖ` norm at most `μ(s)^(1/p) C`. -/
theorem lpNorm_le_of_ae_bound_of_support_subset {f : α → F} {s : Set α} {C : ℝ} {p : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hs : μ s ≠ ⊤) (hfs : Function.support f ⊆ s) (hC : 0 ≤ C)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    lpNorm f p μ ≤ (μ s ^ p.toReal⁻¹).toReal * C := by
  rw [lpNorm, ← ENNReal.toReal_ofReal hC, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hs) ENNReal.ofReal_ne_top)
    (eLpNorm_le_of_ae_bound_of_support_subset hf hfs hfC)

/-- The `Lᵖ(μ)` class of a function supported in a set `s` of finite measure and bounded by `C`
almost everywhere has norm at most `μ(s)^(1/p) C`. -/
theorem MemLp.norm_toLp_le_of_support_subset {f : α → F} {p : ℝ≥0∞} (hf : MemLp f p μ)
    {s : Set α} (hs : μ s ≠ ⊤) (hfs : Function.support f ⊆ s) {C : ℝ} (hC : 0 ≤ C)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    ‖hf.toLp f‖ ≤ (μ s ^ p.toReal⁻¹).toReal * C := by
  rw [Lp.norm_toLp]
  exact lpNorm_le_of_ae_bound_of_support_subset hf.aestronglyMeasurable hs hfs hC hfC

/-- A function vanishing almost everywhere outside a set `s` has the same `Lᵖ` seminorm for `μ` and
for `μ.restrict s`. -/
theorem eLpNorm_restrict_eq_of_ae_compl_eq_zero {f : α → F} {s : Set α} {p : ℝ≥0∞}
    (hs : NullMeasurableSet s μ) (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) :
    eLpNorm f p (μ.restrict s) = eLpNorm f p μ := by
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
  refine eLpNorm_congr_ae ?_
  filter_upwards [hf] with x hx
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs]
  · rw [Set.indicator_of_notMem hxs, hx hxs]

/-- Let `s ⊆ t`. If `f ∈ Lᵖ(μ|t)` vanishes almost everywhere off `s`, then every `g ∈ Lᵖ(μ|s)`
agreeing with `f` almost everywhere on `s` has the same norm as `f`. -/
theorem Lp.norm_eq_norm_of_ae_eq_restrict {s t : Set α} {p : ℝ≥0∞} (hst : s ⊆ t)
    (hs : NullMeasurableSet s (μ.restrict t)) {f : Lp F p (μ.restrict t)}
    {g : Lp F p (μ.restrict s)} (hgf : g =ᵐ[μ.restrict s] f)
    (hf : ∀ᵐ x ∂μ.restrict t, x ∉ s → f x = 0) : ‖g‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hgf, ← Measure.restrict_restrict_of_subset hst,
    eLpNorm_restrict_eq_of_ae_compl_eq_zero hs hf]

end MeasureTheory
