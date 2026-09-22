/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Extended manifold charts as measurable embeddings

Mathlib's extended chart at a point is a `PartialEquiv` between a manifold and its model vector
space. Its restrictions to the chart source and target are mutually continuous, hence the chart
restricted to its source is a measurable embedding for the Borel measurable spaces. This is the
form used to transport measures between a manifold and coordinates.

## Main results

* `TauCeti.measurableEmbedding_extChartAt_restrict`: an extended chart restricted to its source is
  a measurable embedding.
* `TauCeti.MeasurableSet.image_extChartAt`: the image of a measurable subset of a chart source is
  measurable in the model space.
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The Borel measurable space on the model vector space, used in this file. -/
local instance extChartAtMeasurableSpaceE : MeasurableSpace E := borel E

/-- The Borel measurable space on the manifold, used in this file. -/
local instance extChartAtMeasurableSpaceM : MeasurableSpace M := borel M

/-- The model vector space's measurable space is its Borel measurable space. -/
local instance extChartAtBorelSpaceE : BorelSpace E := ⟨rfl⟩

/-- The manifold's measurable space is its Borel measurable space. -/
local instance extChartAtBorelSpaceM : BorelSpace M := ⟨rfl⟩

/-- The extended chart at `x`, restricted to its source, is a measurable embedding for the Borel
measurable spaces. -/
theorem measurableEmbedding_extChartAt_restrict (x : M) :
    MeasurableEmbedding ((extChartAt I x).source.domRestrict (extChartAt I x)) := by
  let e : PartialHomeomorph M E :=
    { toPartialEquiv := extChartAt I x
      continuousOn_toFun := continuousOn_extChartAt x
      continuousOn_invFun := continuousOn_extChartAt_symm x }
  apply e.isEmbedding_restrict.measurableEmbedding
  change MeasurableSet (Set.range ((extChartAt I x).source.domRestrict (extChartAt I x)))
  rw [Set.range_domRestrict, PartialEquiv.image_source_eq_target, extChartAt_target]
  exact ((chartAt H x).open_target.preimage I.continuous_symm).measurableSet.inter
    I.isClosed_range.measurableSet

/-- The image of a measurable subset of an extended chart's source is measurable in the model
space. -/
theorem _root_.MeasurableSet.image_extChartAt {s : Set M} (hs : MeasurableSet s) (x : M)
    (hsource : s ⊆ (extChartAt I x).source) : MeasurableSet ((extChartAt I x) '' s) := by
  rw [← Set.inter_eq_left.mpr hsource, ← Set.image_domRestrict]
  exact (measurableEmbedding_extChartAt_restrict (I := I) x).measurableSet_image.mpr
    (hs.preimage measurable_subtype_coe)

end TauCeti
