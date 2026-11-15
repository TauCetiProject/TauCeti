/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Instances.EuclideanProd

/-!
# Euclidean charts on the two-dimensional torus

`TauCeti.torusChartedSpace` charts `Circle × Circle` on `EuclideanSpace ℝ (Fin 2)`. It is the
specialisation of `TauCeti.prodEuclideanChartedSpace` to two circles, which identifies Mathlib's
product model of the two circle charts with `ℝ²`, and `TauCeti.torusChartedSpace_chartAt`
describes its charts. It is a definition rather than an instance, so that the Euclidean model can
be chosen explicitly alongside Mathlib's product model.
-/

public section

namespace TauCeti

/-- The torus `S¹ × S¹`, charted on `ℝ²` through the product of the circle charts. -/
@[instance_reducible]
noncomputable def torusChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) (Circle × Circle) :=
  prodEuclideanChartedSpace (n := 1) (m := 1)

/-- The chart of `TauCeti.torusChartedSpace` at `x` is the product of the circle charts at `x.1`
and `x.2`, followed by `EuclideanSpace.finAddEquivProd.symm`. -/
@[simp, mfld_simps]
theorem torusChartedSpace_chartAt (x : Circle × Circle) :
    @chartAt _ _ _ _ torusChartedSpace x =
      ((chartAt (EuclideanSpace ℝ (Fin 1)) x.1).prod (chartAt (EuclideanSpace ℝ (Fin 1)) x.2)).trans
        EuclideanSpace.finAddEquivProd.symm.toHomeomorph.toOpenPartialHomeomorph :=
  prodEuclideanChartedSpace_chartAt x

end TauCeti
