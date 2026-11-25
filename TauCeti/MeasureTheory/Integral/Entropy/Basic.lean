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
Entropy is nonnegative for an a.e. nonnegative function under a probability measure, assuming
integrability of the function and its `x log x` transform. The file also gives formulas for
constants, Dirac measures, and scaling the measure.
-/

public section

open scoped ENNReal
open Set

namespace MeasureTheory.Measure

/-- The **entropy** `Ent_μ(g) = ∫ g log g dμ - (∫ g dμ) log (∫ g dμ)` of a function `g`.
This is real-valued even for nonintegrable inputs: each nonintegrable Bochner integral is zero.
It uses `0 log 0 = 0` and, for signed inputs, `Real.log x = Real.log |x|`. -/
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

/-- The entropy of a constant under an arbitrary measure. For infinite total mass,
`μ.real univ` and the entropy are zero. -/
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

/-- Scaling a measure by `c` scales entropy by `c.toReal` and subtracts the scaled integral of
`g` times `Real.log c.toReal`. For `c = ∞`, the real projection and the entropy are zero. -/
theorem entropy_smul_measure {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (c : ℝ≥0∞) (g : α → ℝ) :
    entropy (c • μ) g =
      c.toReal * entropy μ g - (c.toReal * (∫ x, g x ∂μ)) * Real.log c.toReal := by
  simp only [entropy_def, integral_smul_measure, smul_eq_mul]
  have h := Real.negMulLog_mul c.toReal (∫ x, g x ∂μ)
  simp only [Real.negMulLog_eq_neg] at h
  nlinarith

/-- Scaling a function scales its entropy by the same factor, when the function and its
`x log x` transform are integrable. -/
theorem entropy_const_mul {α : Type*} [MeasurableSpace α] (μ : Measure α) (c : ℝ)
    (g : α → ℝ) (hg : Integrable g μ)
    (hlog : Integrable (fun x ↦ g x * Real.log (g x)) μ) :
    entropy μ (fun x ↦ c * g x) = c * entropy μ g := by
  by_cases hc : c = 0
  · simp [entropy_def, hc]
  have hlog_ae : (fun x ↦ (c * g x) * Real.log (c * g x)) =ᵐ[μ]
      fun x ↦ c * (g x * Real.log (g x)) + (c * Real.log c) * g x := by
    filter_upwards with x
    by_cases hx : g x = 0
    · simp [hx]
    · rw [Real.log_mul hc hx]
      ring
  have hlog_integral :
      (∫ x, (c * g x) * Real.log (c * g x) ∂μ) =
        c * (∫ x, g x * Real.log (g x) ∂μ) +
          (c * Real.log c) * (∫ x, g x ∂μ) := by
    rw [integral_congr_ae hlog_ae, integral_add (hlog.const_mul c)
      (hg.const_mul (c * Real.log c)), integral_const_mul, integral_const_mul]
  have hmass : (∫ x, c * g x ∂μ) = c * ∫ x, g x ∂μ := integral_const_mul _ _
  rw [entropy_def, entropy_def, hlog_integral, hmass]
  by_cases hm : (∫ x, g x ∂μ) = 0
  · simp [hm]
  · rw [Real.log_mul hc hm]
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
