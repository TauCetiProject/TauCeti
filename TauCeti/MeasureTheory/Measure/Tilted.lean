/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Kernel.WithDensity

import Mathlib.Probability.Kernel.MeasurableIntegral
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Densities, masses, and parameter measurability of exponentially tilted measures

Mathlib's `MeasureTheory.Measure.tilted` sends a measure `μ` and a potential `f` to the normalized
measure `(∫ exp f ∂μ)⁻¹ • exp f • μ`. This file adds the facts used to identify tilted
members of concrete families of distributions.

* `MeasureTheory.Measure.map_tilted` transports a tilt by a statistic on the target through
  a measurable pushforward.
* `TauCeti.tilted_withDensity`: tilting a measure with density `g` multiplies `g` by the
  normalized weight, so a tilted law with a density again has an explicit density.
* `TauCeti.tilted_singleton`: the mass of a singleton under a tilted measure, which identifies
  tilted laws on countable spaces; `TauCeti.tilted_dirac` records that point masses are fixed.
* `TauCeti.measurable_tilted` and `MeasureTheory.Measure.measurable_tilted`: a jointly measurable
  family of potentials tilts an s-finite kernel, or any fixed measure (s-finite or not), into a
  measurable family of measures for the Giry measurable structure.
-/

public section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal

namespace TauCeti

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- Tilting a measure with density `g` multiplies the density by the normalized exponential
weight. -/
theorem tilted_withDensity {μ : Measure α} {g : α → ℝ≥0∞} (hg : AEMeasurable g μ) {f : α → ℝ}
    (hf : AEMeasurable f μ) :
    (μ.withDensity g).tilted f = μ.withDensity
      (fun x ↦ g x * ENNReal.ofReal (exp (f x) / ∫ y, exp (f y) ∂μ.withDensity g)) := by
  rw [Measure.tilted, ← withDensity_mul₀ hg (by fun_prop), Pi.mul_def]

/-- The mass of a singleton under an exponentially tilted measure. -/
theorem tilted_singleton [MeasurableSingletonClass α] (μ : Measure α) (f : α → ℝ) (a : α) :
    μ.tilted f {a} = ENNReal.ofReal (exp (f a) / ∫ x, exp (f x) ∂μ) * μ {a} := by
  rw [tilted_apply' _ _ (measurableSet_singleton a), lintegral_singleton]

/-- A point mass is unchanged by every tilt. -/
@[simp]
theorem tilted_dirac [MeasurableSingletonClass α] (a : α) (f : α → ℝ) :
    (Measure.dirac a).tilted f = Measure.dirac a := by
  rw [tilted_congr (ae_eq_dirac f)]
  exact tilted_const _ _

/-- **Parameter measurability of tilting.** Tilting the members of an s-finite kernel by a
jointly measurable family of potentials gives a measurable family of measures. -/
theorem measurable_tilted (κ : Kernel β α) [IsSFiniteKernel κ] {f : β → α → ℝ}
    (hf : Measurable (Function.uncurry f)) :
    Measurable fun b ↦ (κ b).tilted (f b) := by
  have hZ : Measurable fun b ↦ ∫ x, exp (f b x) ∂κ b :=
    (measurable_exp.comp hf).stronglyMeasurable.integral_kernel_prod_right'.measurable
  have hw : Measurable (Function.uncurry fun b x ↦
      ENNReal.ofReal (exp (f b x) / ∫ y, exp (f b y) ∂κ b)) :=
    ((measurable_exp.comp hf).div (hZ.comp measurable_fst)).ennreal_ofReal
  have h : (fun b ↦ (κ b).tilted (f b)) = Kernel.withDensity κ fun b x ↦
      ENNReal.ofReal (exp (f b x) / ∫ y, exp (f b y) ∂κ b) := by
    funext b
    rw [Kernel.withDensity_apply _ hw, Measure.tilted]
  rw [h]
  exact (Kernel.withDensity κ _).measurable

end TauCeti

namespace MeasureTheory.Measure

/-- Pushing an exponential tilt forward commutes with tilting by a statistic on the target. -/
theorem map_tilted {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} {g : β → ℝ} (hf : Measurable f) (hg : Measurable g) :
    (μ.tilted (g ∘ f)).map f = (μ.map f).tilted g := by
  rw [Measure.tilted, Measure.tilted, integral_map hf.aemeasurable
    (hg.exp.stronglyMeasurable.aestronglyMeasurable)]
  exact map_withDensity_comp hf ((hg.exp.div_const _).ennreal_ofReal)

/-- **Parameter measurability of tilting a fixed measure.** Tilting a measure by a jointly
measurable family of potentials gives a measurable family of measures. No s-finiteness is needed:
when `μ` is not s-finite, no `exp (f b ·)` is `μ`-integrable and every tilt is zero. -/
theorem measurable_tilted {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : β → α → ℝ} (hf : Measurable (Function.uncurry f)) :
    Measurable fun b ↦ μ.tilted (f b) := by
  by_cases hμ : SFinite μ
  · exact TauCeti.measurable_tilted (ProbabilityTheory.Kernel.const β μ) hf
  · have h0 (b : β) : μ.tilted (f b) = 0 := tilted_of_not_integrable fun hint ↦
      hμ (sfinite_of_absolutelyContinuous (absolutelyContinuous_tilted hint))
    simpa only [h0] using measurable_const

end MeasureTheory.Measure
