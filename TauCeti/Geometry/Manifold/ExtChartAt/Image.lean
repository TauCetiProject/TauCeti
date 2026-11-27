/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Images of open sets in extended charts

For a boundaryless model, the extended chart at a point maps open subsets of its source to open
subsets of the model vector space (`IsOpen.image_extChartAt`): the image is the preimage of the
set under the continuous inverse chart, inside the open chart target. This is the open-set
counterpart of `MeasurableSet.image_extChartAt`.
-/

public section

open Set
open scoped Manifold

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M]

/-- For a boundaryless model, the image in the extended chart at `x` of an open subset of its
source is open. -/
theorem IsOpen.image_extChartAt {s : Set M} (hs : IsOpen s) (x : M)
    (hsub : s ⊆ (extChartAt I x).source) : IsOpen (extChartAt I x '' s) := by
  rw [← inter_eq_right.2 hsub, (extChartAt I x).image_source_inter_eq']
  exact (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x) hs
