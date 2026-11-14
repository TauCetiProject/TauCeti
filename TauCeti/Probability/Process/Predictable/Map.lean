/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Predictable.Measure

/-!
# Predictable maps between filtered sample spaces

A sample-space map measurable at each time induces a measurable map of predictable
sigma-algebras by leaving time unchanged. If it preserves the sample measures, it also
preserves their finite-horizon predictable measures. Consequently native Lᵖ pullback
transports predictable integrands without changing their expected energy.

These statements allow different ambient measurable spaces, as needed when comparing
stochastic integrals before and after completing a probability space. They do not assert
that an arbitrary enlargement of a filtration preserves Brownian increment independence.
-/

public section

open MeasureTheory Set TauCeti.Probability
open scoped NNReal

namespace MeasureTheory.Filtration

variable {ι Ω Ω' : Type*} {m : MeasurableSpace Ω} {m' : MeasurableSpace Ω'}

/-- A sample-space map measurable at every time is measurable on predictable
sigma-algebras when time is left unchanged. -/
theorem measurable_prodMap_predictable [LinearOrder ι] [OrderBot ι]
    (ℱ : Filtration ι m) (𝒢 : Filtration ι m') {f : Ω → Ω'}
    (hf : ∀ t, Measurable[ℱ t, 𝒢 t] f) :
    @Measurable (ι × Ω) (ι × Ω') ℱ.predictable 𝒢.predictable (Prod.map id f) := by
  rw [measurable_iff_comap_le, MeasurableSpace.comap_le_iff_le_map]
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact measurableSet_predictable_singleton_bot_prod (hf ⊥ hA)
  · intro t A hA
    exact measurableSet_predictable_Ioi_prod (hf t hA)

/-- A filtered measure-preserving sample map preserves finite-horizon predictable
measures. The ambient spaces and the filtrations on its two sides may differ. -/
theorem measurePreserving_prodMap_predictableMeasure
    (ℱ : Filtration ℝ≥0 m) (𝒢 : Filtration ℝ≥0 m')
    {P : Measure Ω} {Q : Measure Ω'} [SFinite P] {f : Ω → Ω'}
    (hf : MeasurePreserving f P Q) (hℱ : ∀ t, Measurable[ℱ t, 𝒢 t] f) (T : ℝ≥0) :
    @MeasurePreserving (ℝ≥0 × Ω) (ℝ≥0 × Ω') ℱ.predictable 𝒢.predictable
      (Prod.map id f) (ℱ.predictableMeasure P T) (𝒢.predictableMeasure Q T) := by
  have hm := ℱ.measurable_prodMap_predictable 𝒢 hℱ
  refine @MeasurePreserving.mk _ _ ℱ.predictable 𝒢.predictable _ _ _ hm ?_
  apply @Measure.ext _ 𝒢.predictable
  intro A hA
  rw [Measure.map_apply hm hA, ℱ.predictableMeasure_apply P T (hm hA),
    𝒢.predictableMeasure_apply Q T hA]
  exact ((MeasurePreserving.id (timeMeasure T)).prod hf).measure_preimage
    (𝒢.predictable_le_prod A hA).nullMeasurableSet

end MeasureTheory.Filtration
