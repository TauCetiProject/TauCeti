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
and `MeasureTheory.setLIntegral_congr_fun₀`). It also records the matching upper bound: if
`μ t ≤ m` and `f x · m ≤ w` on `t`, then `∫_t f dμ ≤ w`, with no measurability assumptions.

## Main statements

* `TauCeti.setLIntegral_mono_ae'₀`: monotonicity of the set Lebesgue integral over a
  null-measurable set from an almost-everywhere bound on the set.
* `TauCeti.setLIntegral_mono'₀`: monotonicity of the set Lebesgue integral over a null-measurable
  set from a pointwise bound on the set.
* `TauCeti.mul_measure_le_setLIntegral_ae₀`: if `c ≤ f x` for `μ`-almost every `x ∈ s` and `s` is
  null-measurable, then `c * μ s ≤ ∫⁻ x in s, f x ∂μ`.
* `TauCeti.mul_measure_le_setLIntegral₀`: pointwise form of
  `TauCeti.mul_measure_le_setLIntegral_ae₀`.
* `TauCeti.setLIntegral_le_of_measure_le_of_forall_mul_le`: if `μ t ≤ m` and `f x * m ≤ w` for
  every `x ∈ t`, then `∫⁻ x in t, f x ∂μ ≤ w`.
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

/-- If `μ t ≤ m` and `f x · m ≤ w` on `t`, then the integral of `f` over `t` is at most `w`.
Neither `f` nor `t` needs to be measurable. -/
theorem setLIntegral_le_of_measure_le_of_forall_mul_le {f : α → ℝ≥0∞} {t : Set α} {m w : ℝ≥0∞}
    (hm : μ t ≤ m) (h : ∀ x ∈ t, f x * m ≤ w) : ∫⁻ x in t, f x ∂μ ≤ w := by
  rcases eq_or_ne m 0 with h0 | h0
  · rw [setLIntegral_measure_zero _ _ (nonpos_iff_eq_zero.1 (h0 ▸ hm))]
    exact zero_le
  rcases eq_or_ne w ∞ with htop | htop
  · exact htop ▸ le_top
  calc ∫⁻ x in t, f x ∂μ
    _ ≤ ∫⁻ _ in t, w / m ∂μ := setLIntegral_mono measurable_const fun x hx ↦
        (ENNReal.le_div_iff_mul_le (.inl h0) (.inr htop)).2 (h x hx)
    _ = w / m * μ t := setLIntegral_const t _
    _ ≤ m * (w / m) := by rw [mul_comm]; gcongr
    _ ≤ w := ENNReal.mul_div_le

end TauCeti
