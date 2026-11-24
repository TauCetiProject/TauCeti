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

An open subset `W` of a charted space `X` is a charted space
(`TopologicalSpace.Opens.instChartedSpace`). Viewed as an object `(Opens.toTopCat X).obj W` of
`TopCat`, as in the Mayer–Vietoris sequences indexed by `Opens X`, it is a charted space by the
same atlas (`TopologicalSpace.Opens.instChartedSpaceToTopCatObj`).
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TopologicalSpace.Opens

/-- An open subset of a charted space, viewed as an object of `TopCat`, is a charted space. -/
instance instChartedSpaceToTopCatObj {H : Type*} [TopologicalSpace H] {X : TopCat.{u}}
    [ChartedSpace H X] (W : Opens X) : ChartedSpace H ((toTopCat X).obj W) :=
  TopologicalSpace.Opens.instChartedSpace (H := H) (M := X) W

end TopologicalSpace.Opens
