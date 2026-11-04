/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Entropy of a function with respect to a measure

Defines the entropy `Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)`.
-/

public section

namespace MeasureTheory.Measure

/-- The **entropy** `Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)` of a function `g`, with the
convention `0 log 0 = 0` of `Real.log`. -/
noncomputable def entropy {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) (g : α → ℝ) : ℝ :=
  ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

/-- The defining equation for measure entropy. -/
theorem entropy_def {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) (g : α → ℝ) :
    entropy μ g =
      ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ) :=
  (rfl)

@[simp]
theorem entropy_zero {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) :
    entropy μ (fun _ ↦ (0 : ℝ)) = 0 := by
  simp [entropy]

@[simp]
theorem entropy_zero_measure {α : Type*} {mα : MeasurableSpace α} (g : α → ℝ) :
    entropy (0 : Measure α) g = 0 := by
  simp [entropy]

/-- Entropy is preserved by transporting both the measure and function through a measurable
embedding. -/
theorem entropy_map {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} {φ : α → β} (hφ : MeasurableEmbedding φ) (g : β → ℝ) :
    entropy (μ.map φ) g = entropy μ (g ∘ φ) := by
  simp only [entropy, hφ.integral_map, Function.comp_apply]

end MeasureTheory.Measure
