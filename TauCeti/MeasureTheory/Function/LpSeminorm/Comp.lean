/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Precomposition by a map with dominated pushforward

Let `f : α → β` be almost everywhere measurable for `μ`. If `μ.map f ≤ C • ν`, then
`eLpNorm (g ∘ f) p μ ≤ C ^ (1/p) * eLpNorm g p ν` for every `p`
(`MeasureTheory.eLpNorm_comp_le_of_map_le_smul`). The codomain only needs a continuous
extended norm. For a normed vector space codomain, `C < ⊤`, and `1 ≤ p`, this estimate gives
boundedness of precomposition from `Lᵖ(ν)` to `Lᵖ(μ)`, with norm at most `C ^ (1/p)`.

## Main declarations

* `MeasureTheory.eLpNorm_comp_le_of_map_le_smul`: the `eLpNorm` bound for precomposition.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α β ε : Type*} [MeasurableSpace α] [MeasurableSpace β] [TopologicalSpace ε]
  [ContinuousENorm ε] {μ : Measure α} {ν : Measure β} {f : α → β} {g : β → ε}

/-- **`eLpNorm` bound for precomposition.** If `f` pushes `μ` forward to at most `C • ν`, then
`eLpNorm (g ∘ f) p μ ≤ C ^ (1/p) * eLpNorm g p ν`. No measurability assumption on `g` is
needed: its `eLpNorm` is infinite when it is not almost everywhere strongly measurable. -/
theorem eLpNorm_comp_le_of_map_le_smul {C : ℝ≥0∞} (hf : AEMeasurable f μ) (hmap : μ.map f ≤ C • ν)
    (p : ℝ≥0∞) :
    eLpNorm (g ∘ f) p μ ≤ C ^ (1 / p).toReal * eLpNorm g p ν := by
  by_cases hC : C = 0
  · have hμ : μ = 0 := (Measure.map_eq_zero_iff hf).1
      (le_antisymm (by simpa [hC] using hmap) bot_le)
    simp [hμ]
  by_cases hg : AEStronglyMeasurable g ν
  · rw [← eLpNorm_map_measure (hg.mono_ac (Measure.absolutelyContinuous_of_le_smul hmap)) hf]
    exact eLpNorm_le_of_measure_le_smul hmap
  rw [eLpNorm_of_not_aestronglyMeasurable hg,
    ENNReal.mul_top (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hC)
      ENNReal.toReal_nonneg).ne']
  exact le_top

end MeasureTheory
