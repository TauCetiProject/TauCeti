/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.HasGroupoid
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Open subsets of a charted space as objects of `TopCat`

An open subset `V` of a topological space `X` enters `TopCat` as the object
`(TopologicalSpace.Opens.toTopCat X).obj V`, which is the subtype `V` only by definition. Mathlib
makes the subtype of an open subset of a charted space a charted space
(`TopologicalSpace.Opens.instChartedSpace`); this file transfers that structure to the `TopCat`
object, as `TopologicalSpace.Opens.t2Space_toTopCat_obj` does for the Hausdorff property.

## Main instances

* `TopologicalSpace.Opens.instChartedSpaceToTopCatObj`: an open subset of a charted space, as an
  object of `TopCat`, is a charted space.
-/

public noncomputable section

/-- An open subset of a charted space, as an object of `TopCat`, is a charted space, like the
subtype. -/
instance TopologicalSpace.Opens.instChartedSpaceToTopCatObj {H : Type*} [TopologicalSpace H]
    {X : TopCat} [ChartedSpace H X] (V : Opens X) : ChartedSpace H ((Opens.toTopCat X).obj V) :=
  inferInstanceAs (ChartedSpace H V)

end
