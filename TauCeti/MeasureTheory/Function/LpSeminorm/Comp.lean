/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Precomposition by a map with dominated pushforward

Let `f : α → β` be almost everywhere measurable for `μ`. If `μ.map f ≪ ν`, then precomposition
with `f` preserves almost-everywhere strong measurability
(`MeasureTheory.AEStronglyMeasurable.comp_aemeasurable_of_map_absolutelyContinuous`). If moreover
`μ.map f ≤ C • ν`, then `eLpNorm (g ∘ f) p μ ≤ C ^ (1/p) * eLpNorm g p ν` for every `p`
(`MeasureTheory.eLpNorm_comp_le_of_map_le_smul`). For `C < ⊤` and `1 ≤ p` this makes
precomposition with `f` a bounded operator from `Lᵖ(ν)` to `Lᵖ(μ)`, of norm at most `C ^ (1/p)`.

## Main declarations

* `MeasureTheory.AEStronglyMeasurable.comp_aemeasurable_of_map_absolutelyContinuous`:
  precomposition preserves almost-everywhere strong measurability.
* `MeasureTheory.eLpNorm_comp_le_of_map_le_smul`: the `eLpNorm` bound for precomposition.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup F]
  {μ : Measure α} {ν : Measure β} {f : α → β} {g : β → F}

/-- If `μ.map f ≪ ν`, precomposition with `f` takes functions almost everywhere strongly
measurable for `ν` to functions almost everywhere strongly measurable for `μ`. -/
theorem AEStronglyMeasurable.comp_aemeasurable_of_map_absolutelyContinuous
    (hg : AEStronglyMeasurable g ν) (hf : AEMeasurable f μ) (hmap : μ.map f ≪ ν) :
    AEStronglyMeasurable (g ∘ f) μ :=
  (hg.mono_ac hmap).comp_aemeasurable hf

/-- **`eLpNorm` bound for precomposition.** If `f` pushes `μ` forward to at most `C • ν`, then
`eLpNorm (g ∘ f) p μ ≤ C ^ (1/p) * eLpNorm g p ν`. For `C < ⊤` and `1 ≤ p`, this makes
precomposition with `f` a bounded operator from `Lᵖ(ν)` to `Lᵖ(μ)` of norm at most `C ^ (1/p)`. -/
theorem eLpNorm_comp_le_of_map_le_smul {C : ℝ≥0∞} (hf : AEMeasurable f μ) (hmap : μ.map f ≤ C • ν)
    (hg : AEStronglyMeasurable g ν) (p : ℝ≥0∞) :
    eLpNorm (g ∘ f) p μ ≤ C ^ (1 / p).toReal * eLpNorm g p ν := by
  rw [← eLpNorm_map_measure (hg.mono_ac (Measure.absolutelyContinuous_of_le_smul hmap)) hf]
  exact eLpNorm_le_of_measure_le_smul hmap

end MeasureTheory
