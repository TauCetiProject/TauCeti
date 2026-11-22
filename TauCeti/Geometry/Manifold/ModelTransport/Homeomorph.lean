/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# Changing the model space along a homeomorphism

Following every chart of a charted space `M` on `H` with a homeomorphism `Φ : H ≃ₜ H'` gives
charts of `M` on `H'` (`Homeomorph.chartedSpaceComp`), whose chart at a point is the chart of `M`
followed by `Φ` (`Homeomorph.chartAt_chartedSpaceComp`); its atlas consists of the charts of `M`
followed by `Φ` (`Homeomorph.atlas_chartedSpaceComp`).
-/

public section

open Set
open scoped Manifold

variable {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']

namespace Homeomorph

/-- The charts of `M` modelled on `H'` obtained by following each chart of `M` with a
homeomorphism of models `Φ`: the composite charts `ChartedSpace.comp H' H M`, where `H` carries
the single chart `Φ`. -/
@[instance_reducible]
def chartedSpaceComp (Φ : H ≃ₜ H') (M : Type*) [TopologicalSpace M] [ChartedSpace H M] :
    ChartedSpace H' M :=
  letI := Φ.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  ChartedSpace.comp H' H M

/-- The chart of `Φ.chartedSpaceComp M` at `x` is the chart of `M` at `x` followed by `Φ`. -/
theorem chartAt_chartedSpaceComp (Φ : H ≃ₜ H') {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] (x : M) :
    @chartAt H' _ M _ (Φ.chartedSpaceComp M) x = chartAt H x ≫ₕ Φ.toOpenPartialHomeomorph := by
  rw [chartedSpaceComp, chartAt_comp, OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq]

/-- The atlas of `Φ.chartedSpaceComp M` consists of the charts of `M` followed by `Φ`. -/
theorem atlas_chartedSpaceComp (Φ : H ≃ₜ H') (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] :
    @atlas H' _ M _ (Φ.chartedSpaceComp M) = (· ≫ₕ Φ.toOpenPartialHomeomorph) '' atlas H M := by
  rw [chartedSpaceComp]
  -- `ChartedSpace.comp` stores its atlas as `image2 trans (atlas H M) (atlas H' H)`, and the
  -- atlas of the single chart `Φ` is that chart alone; both are fields, not rewrite targets.
  change image2 OpenPartialHomeomorph.trans (atlas H M) {Φ.toOpenPartialHomeomorph} = _
  exact image2_singleton_right

end Homeomorph
