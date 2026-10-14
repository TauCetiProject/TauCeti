/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Euclidean charts on the two-dimensional torus

`TauCeti.torusChartedSpace` charts `Circle × Circle` on `EuclideanSpace ℝ (Fin 2)` by identifying
Mathlib's product model of the two circle charts with `ℝ²`. It is a definition rather than an
instance, so that the Euclidean model can be chosen explicitly alongside Mathlib's product model.
-/

public section

namespace TauCeti

/-- The torus `S¹ × S¹`, charted on `ℝ²` through the product of the circle charts. -/
@[instance_reducible]
noncomputable def torusChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) (Circle × Circle) :=
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2))
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) :=
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 1) (m := 1)).symm.toHomeomorph
      |>.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  ChartedSpace.comp _ (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) _

end TauCeti
