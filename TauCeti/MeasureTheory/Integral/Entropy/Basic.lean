/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Entropy of a function with respect to a measure

Defines the entropy `Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)`.
-/

public section

open scoped ENNReal
open Set

namespace MeasureTheory.Measure

/-- The **entropy** `Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)` of a function `g`, with the
convention `0 log 0 = 0` of `Real.log`. -/
noncomputable def entropy {α : Type*} {_ : MeasurableSpace α} (μ : Measure α) (g : α → ℝ) : ℝ :=
  ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ)

/-- The defining equation for measure entropy. -/
theorem entropy_def {α : Type*} {_ : MeasurableSpace α} (μ : Measure α) (g : α → ℝ) :
    entropy μ g =
      ∫ x, g x * Real.log (g x) ∂μ - (∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ) :=
  (rfl)

/-- Entropy depends only on the almost-everywhere equivalence class of a function. -/
theorem entropy_congr_ae {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    {f g : α → ℝ} (h : f =ᵐ[μ] g) : entropy μ f = entropy μ g := by
  have hlog : (fun x ↦ f x * Real.log (f x)) =ᵐ[μ]
      (fun x ↦ g x * Real.log (g x)) := by
    filter_upwards [h] with x hx
    rw [hx]
  simp only [entropy_def, integral_congr_ae h, integral_congr_ae hlog]

@[simp]
theorem entropy_zero {α : Type*} {mα : MeasurableSpace α} (μ : Measure α) :
    entropy μ (fun _ ↦ (0 : ℝ)) = 0 := by
  simp [entropy]

@[simp]
theorem entropy_zero_measure {α : Type*} {mα : MeasurableSpace α} (g : α → ℝ) :
    entropy (0 : Measure α) g = 0 := by
  simp [entropy]

/-- The entropy of a constant under an arbitrary measure. -/
theorem entropy_const {α : Type*} [MeasurableSpace α] (μ : Measure α) (c : ℝ) :
    entropy μ (fun _ ↦ c) =
      μ.real univ * (c * Real.log c) -
        (μ.real univ * c) * Real.log (μ.real univ * c) := by
  simp [entropy_def, integral_const, smul_eq_mul]

@[simp]
theorem entropy_const_of_isProbabilityMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (c : ℝ) :
    entropy μ (fun _ ↦ c) = 0 := by
  simp [entropy_const, probReal_univ]

@[simp]
theorem entropy_dirac {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (a : α) (g : α → ℝ) : entropy (dirac a) g = 0 := by
  simp [entropy_def]

/-- Scaling a measure scales entropy and adds the correction for its new total mass. -/
theorem entropy_smul_measure {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c : ℝ≥0∞) (g : α → ℝ) :
    entropy (c • μ) g =
      c.toReal * entropy μ g - (c.toReal * (∫ x, g x ∂μ)) * Real.log c.toReal := by
  simp only [entropy_def, integral_smul_measure, smul_eq_mul]
  by_cases hc : c.toReal = 0
  · simp [hc]
  by_cases hg : (∫ x, g x ∂μ) = 0
  · simp [hg]
  rw [Real.log_mul hc hg]
  ring

/-- Functional entropy is nonnegative under a probability measure for an a.e. nonnegative
function, when the function and its `x log x` transform are integrable. -/
theorem entropy_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {g : α → ℝ} (hg : 0 ≤ᵐ[μ] g)
    (hgi : Integrable g μ) (hlog : Integrable (fun x ↦ g x * Real.log (g x)) μ) :
    0 ≤ entropy μ g := by
  have h := Real.convexOn_mul_log.map_integral_le Real.continuous_mul_log.continuousOn
    isClosed_Ici hg hgi hlog
  rw [entropy_def]
  linarith

/-- Entropy is preserved by transporting both the measure and function through a measurable
embedding. -/
theorem entropy_map {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} {φ : α → β} (hφ : MeasurableEmbedding φ) (g : β → ℝ) :
    entropy (μ.map φ) g = entropy μ (g ∘ φ) := by
  simp only [entropy, hφ.integral_map, Function.comp_apply]

end MeasureTheory.Measure
