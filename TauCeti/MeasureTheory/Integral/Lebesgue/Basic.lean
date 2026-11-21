/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Additional lemmas for the lower Lebesgue integral

This file records null-measurable monotonicity and constant lower bounds for set Lebesgue integrals,
extending Mathlib's `MeasureTheory.setLIntegral_mono_ae'` and `MeasureTheory.setLIntegral_mono'`
from `MeasurableSet` to `NullMeasurableSet` (parallel to `MeasureTheory.setLIntegral_congr_fun_ae₀`
and `MeasureTheory.setLIntegral_congr_fun₀`).

## Main statements

* `TauCeti.setLIntegral_mono_ae'₀`: monotonicity of the set Lebesgue integral over a
  null-measurable set from an almost-everywhere bound on the set.
* `TauCeti.setLIntegral_mono'₀`: monotonicity of the set Lebesgue integral over a null-measurable
  set from a pointwise bound on the set.
* `TauCeti.mul_measure_le_setLIntegral_ae₀`: if `c ≤ f x` for `μ`-almost every `x ∈ s` and `s` is
  null-measurable, then `c * μ s ≤ ∫⁻ x in s, f x ∂μ`.
* `TauCeti.mul_measure_le_setLIntegral₀`: pointwise form of
  `TauCeti.mul_measure_le_setLIntegral_ae₀`.
-/

public section

namespace TauCeti

open Filter MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Monotonicity of the set Lebesgue integral over a null-measurable set, under an
almost-everywhere bound on the set. This extends Mathlib's `MeasureTheory.setLIntegral_mono_ae'`
from `MeasurableSet` to `NullMeasurableSet`. -/
theorem setLIntegral_mono_ae'₀ {s : Set α} {f g : α → ℝ≥0∞} (hs : NullMeasurableSet s μ)
    (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  lintegral_mono_ae <| (ae_restrict_iff'₀ hs).2 hfg

/-- Monotonicity of the set Lebesgue integral over a null-measurable set, under a pointwise bound
on the set. This extends Mathlib's `MeasureTheory.setLIntegral_mono'` from `MeasurableSet` to
`NullMeasurableSet`. -/
theorem setLIntegral_mono'₀ {s : Set α} {f g : α → ℝ≥0∞} (hs : NullMeasurableSet s μ)
    (hfg : ∀ x ∈ s, f x ≤ g x) : ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
  setLIntegral_mono_ae'₀ hs (ae_of_all _ hfg)

/-- If `c ≤ f x` for `μ`-almost every `x ∈ s` and `s` is null-measurable, then
`c * μ s ≤ ∫⁻ x in s, f x ∂μ`. -/
theorem mul_measure_le_setLIntegral_ae₀ {s : Set α} {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hs : NullMeasurableSet s μ) (hcf : ∀ᵐ x ∂μ, x ∈ s → c ≤ f x) :
    c * μ s ≤ ∫⁻ x in s, f x ∂μ := by
  rw [← setLIntegral_const]
  exact setLIntegral_mono_ae'₀ hs hcf

/-- If `c ≤ f x` for every `x ∈ s` and `s` is null-measurable, then
`c * μ s ≤ ∫⁻ x in s, f x ∂μ`. -/
theorem mul_measure_le_setLIntegral₀ {s : Set α} {f : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hs : NullMeasurableSet s μ) (hcf : ∀ x ∈ s, c ≤ f x) :
    c * μ s ≤ ∫⁻ x in s, f x ∂μ :=
  mul_measure_le_setLIntegral_ae₀ hs (ae_of_all _ hcf)

end TauCeti
