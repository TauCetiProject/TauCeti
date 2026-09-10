/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Pushing a weighted measure forward

A weight travels with the measure it weights: along a measurable equivalence `e`, the image of
`μ.withDensity f` is the image of `μ` weighted by `f ∘ e.symm`. Mathlib has this only for the
special case of a Radon–Nikodym derivative, in
`MeasurableEmbedding.map_withDensity_rnDeriv`.

Combined with a rescaling law for the measure itself, such as
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar` on a finite-dimensional real normed
space, this is what turns a density for one member of a family of measures into a density for its
images.
-/
public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace MeasurableEquiv

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **A weight travels with the measure it weights.** Pushing `μ.withDensity f` forward along a
measurable equivalence `e` gives the pushforward of `μ` weighted by `f ∘ e.symm`.

No measurability of `f` is needed: on a measurable set both sides unfold to the lower integral of
`f` over the preimage, and `MeasureTheory.lintegral_map_equiv` transports that integral along `e`
with no hypothesis on the integrand. -/
theorem map_withDensity (e : α ≃ᵐ β) (μ : Measure α) (f : α → ℝ≥0∞) :
    (μ.withDensity f).map e = (μ.map e).withDensity fun y => f (e.symm y) := by
  ext s hs
  rw [withDensity_apply _ hs, Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), Measure.restrict_map e.measurable hs,
    lintegral_map_equiv]
  simp only [MeasurableEquiv.symm_apply_apply]

end MeasurableEquiv
