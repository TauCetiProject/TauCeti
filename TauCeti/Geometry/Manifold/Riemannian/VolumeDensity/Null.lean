/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import TauCeti.Geometry.Manifold.Measure.PositiveDensity
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Null sets for the Riemannian volume

In each chart, the Riemannian volume of a continuous metric is Haar measure weighted by the chart
volume density, which is continuous and positive. So the Riemannian volume is a positive
continuous density measure (`TauCeti.IsPositiveDensityMeasure`), and a set has Riemannian volume
zero exactly when its images in the charts are null for Haar measure. In other words, the null sets
of `TauCeti.riemannianVolume` are the chartwise null sets `TauCeti.IsNullSet`. This makes
chartwise results such as Sard's theorem apply to the Riemannian volume, also on manifolds with
boundary or corners.

## Main results

* `TauCeti.isPositiveDensityMeasure_riemannianVolume`: the Riemannian volume is a positive
  continuous density measure.
* `TauCeti.riemannianVolume_eq_zero_iff_image_of_subset`: a subset of a chart source has volume
  zero exactly when its image in the chart is null for an additive Haar measure.
* `TauCeti.isNullSet_iff_riemannianVolume_eq_zero`: a set is chartwise null exactly when it has
  Riemannian volume zero.
* `TauCeti.ae_riemannianVolume`: almost everywhere for the Riemannian volume of any continuous
  metric means almost everywhere for the chartwise null sets, `TauCeti.Manifold.ae I M`.
* `TauCeti.nullSingletonClass_riemannianVolume`: on a manifold of positive dimension, every point
  has Riemannian volume zero.
-/

public noncomputable section

open Bundle MeasureTheory Set
open scoped ENNReal Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

section Null

variable [MeasurableSpace E] [BorelSpace E]

/-- The Riemannian volume of a continuous metric is a positive continuous density measure. -/
theorem isPositiveDensityMeasure_riemannianVolume :
    IsPositiveDensityMeasure I (riemannianVolume I M) := by
  obtain rfl : ‹MeasurableSpace E› = extChartAtMeasurableSpaceE := BorelSpace.measurable_eq
  let : MeasurableSpace E := extChartAtMeasurableSpaceE
  rw [isPositiveDensityMeasure_iff_of_isAddHaarMeasure (Module.finBasis ℝ E).addHaar]
  intro x
  let e := extChartAt I x
  refine ⟨fun y ↦ chartVolumeDensity (I := I) x (e.symm y),
    continuousOn_chartVolumeDensity_extChartAt_symm x, fun y hy ↦ chartVolumeDensity_pos x ?_, ?_⟩
  · simpa only [TangentBundle.trivializationAt_baseSet, e, extChartAt_source] using e.map_target hy
  ext A hA
  have hsrc : MeasurableSet e.source := (isOpen_extChartAt_source x).measurableSet
  have hpre : MeasurableSet (e ⁻¹' A ∩ e.source) :=
    (continuousOn_extChartAt x).measurableSet_preimage_inter hsrc hA
  have hsub : e ⁻¹' A ∩ e.source ⊆ (chartAt H x).source := by
    simpa only [e, extChartAt_source] using inter_subset_right
  rw [map_restrict_extChartAt_source_apply x hA, riemannianVolume_apply_of_subset hsub,
    chartRiemannianVolume_apply x hpre, withDensity_apply _ hA, Measure.restrict_restrict hA,
    inter_assoc, inter_self, image_preimage_inter, e.image_source_eq_target]

/-- A subset of the source of an extended chart has Riemannian volume zero exactly when its image
in the chart is null for an additive Haar measure. The set need not be measurable. -/
theorem riemannianVolume_eq_zero_iff_image_of_subset {α : M} {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source) (μ : Measure E) [μ.IsAddHaarMeasure] :
    riemannianVolume I M s = 0 ↔ μ ((extChartAt I α) '' s) = 0 :=
  isPositiveDensityMeasure_riemannianVolume.measure_eq_zero_iff_image_of_subset hsub μ

/-- A set is chartwise null exactly when it has Riemannian volume zero. -/
theorem isNullSet_iff_riemannianVolume_eq_zero {s : Set M} :
    IsNullSet I s ↔ riemannianVolume I M s = 0 :=
  isPositiveDensityMeasure_riemannianVolume.isNullSet_iff_measure_eq_zero

/-- A chartwise null set has Riemannian volume zero. -/
theorem IsNullSet.riemannianVolume_eq_zero {s : Set M} (hs : IsNullSet I s) :
    riemannianVolume I M s = 0 := isNullSet_iff_riemannianVolume_eq_zero.mp hs

/-- **Almost everywhere does not depend on the metric.** The almost-everywhere filter of the
Riemannian volume of a continuous metric is the almost-everywhere filter of chartwise null sets. -/
theorem ae_riemannianVolume : ae (riemannianVolume I M) = Manifold.ae I M :=
  isPositiveDensityMeasure_riemannianVolume.ae_eq

end Null

section NullSingleton

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- On a manifold of positive dimension, every point has Riemannian volume zero. -/
instance nullSingletonClass_riemannianVolume [Nontrivial E] :
    NullSingletonClass (riemannianVolume I M) :=
  isPositiveDensityMeasure_riemannianVolume.nullSingletonClass

end NullSingleton

end TauCeti
