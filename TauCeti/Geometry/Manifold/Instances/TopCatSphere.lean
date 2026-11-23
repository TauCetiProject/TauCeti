/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.AlgebraicTopology.Disk
public import TauCeti.Geometry.Manifold.ModelTransport.Finrank

/-!
# The manifold structure of `TopCat.sphere`

The `n`-sphere `TopCat.sphere.{u} n` of Mathlib's `TopCat` is the lift to `Type u` of the unit
sphere of `ℝⁿ⁺¹`. This file makes it a charted space modelled on `ULift.{u} (Fin n) → ℝ`, a model
in the same universe, so that theorems about topological manifolds whose model and manifold share a
universe apply to it (`TauCeti.TopCat.chartedSpaceSphere`). The charts are Mathlib's stereographic
charts of the unit sphere (`EuclideanSpace.instChartedSpaceSphere`), transported along the lift
`Homeomorph.ulift` and recharted to the model in `Type u` along the equality of dimensions
(`ChartedSpace.ofFinrankEq`).

Together with the instances of `TauCeti.AlgebraicTopology.Disk`, which make the sphere Hausdorff
and compact (`TauCeti.TopCat.t2Space_sphere`, `TauCeti.TopCat.compactSpace_sphere`) and in positive
dimension connected (`TauCeti.TopCat.pathConnectedSpace_sphere`), this makes it a closed connected
manifold.
-/

public section

noncomputable section

universe u

namespace TauCeti.TopCat

/-- The `n`-sphere `TopCat.sphere n`, the lift of the unit sphere of `ℝⁿ⁺¹`, is a charted space
modelled on `ULift (Fin n) → ℝ`, by the stereographic charts of the unit sphere. -/
instance chartedSpaceSphere (n : ℕ) :
    ChartedSpace (ULift.{u} (Fin n) → ℝ) (TopCat.sphere.{u} n) :=
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) (TopCat.sphere.{u} n) :=
    Homeomorph.ulift.symm.chartedSpace
  ChartedSpace.ofFinrankEq (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n)) _ (by simp)

end TauCeti.TopCat
