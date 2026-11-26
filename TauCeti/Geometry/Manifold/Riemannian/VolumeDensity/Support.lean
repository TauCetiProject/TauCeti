/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Full support of Riemannian volume

The Riemannian volume measure of a continuous finite-dimensional Riemannian manifold is positive on
nonempty open sets. This gives the full-support interface used by later integration and positivity
arguments.
-/

public section

open Bundle MeasureTheory Set
open scoped Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

attribute [local instance] extChartAtMeasurableSpaceE extChartAtBorelSpaceE

/-- Riemannian volume is positive on every nonempty open set. -/
instance isOpenPosMeasure_riemannianVolume :
    Measure.IsOpenPosMeasure (riemannianVolume I M) :=
  isPositiveDensityMeasure_riemannianVolume.isOpenPosMeasure

end TauCeti

end
