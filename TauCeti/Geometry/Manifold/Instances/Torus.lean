/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Euclidean charts on products and on the two-dimensional torus

Mathlib charts a product `M × N` of spaces charted on `H` and `H'` on the type synonym
`ModelProd H H'`. For spaces charted on Euclidean spaces this file reads those product charts on a
single Euclidean space:

* `TauCeti.prodEuclideanChartedSpace` charts `M × N` on `EuclideanSpace 𝕜 (Fin (n + m))` when `M`
  and `N` are charted on `EuclideanSpace 𝕜 (Fin n)` and `EuclideanSpace 𝕜 (Fin m)`, by composing
  the product charts with `EuclideanSpace.finAddEquivProd`;
* `TauCeti.torusChartedSpace` is its specialisation to the torus `Circle × Circle`, charted on
  `EuclideanSpace ℝ (Fin 2)`.

Both are definitions rather than instances, so that the Euclidean model can be chosen explicitly
alongside Mathlib's product model.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace 𝕜 (Fin n)) M] [ChartedSpace (EuclideanSpace 𝕜 (Fin m)) N]

/-- The product `M × N` of spaces charted on `𝕜ⁿ` and `𝕜ᵐ`, charted on `𝕜ⁿ⁺ᵐ`: the product of
charts of `M` and `N`, followed by the identification `EuclideanSpace.finAddEquivProd` of
`𝕜ⁿ × 𝕜ᵐ` with `𝕜ⁿ⁺ᵐ`. -/
@[instance_reducible]
noncomputable def prodEuclideanChartedSpace :
    ChartedSpace (EuclideanSpace 𝕜 (Fin (n + m))) (M × N) :=
  letI : ChartedSpace (EuclideanSpace 𝕜 (Fin (n + m)))
      (ModelProd (EuclideanSpace 𝕜 (Fin n)) (EuclideanSpace 𝕜 (Fin m))) :=
    (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.toHomeomorph.toOpenPartialHomeomorph
      |>.singletonChartedSpace (by simp)
  ChartedSpace.comp _ (ModelProd (EuclideanSpace 𝕜 (Fin n)) (EuclideanSpace 𝕜 (Fin m))) _

/-- The chart of `TauCeti.prodEuclideanChartedSpace` at `x` is the product of the charts of the
factors at `x.1` and `x.2`, followed by `EuclideanSpace.finAddEquivProd.symm`. -/
theorem prodEuclideanChartedSpace_chartAt (x : M × N) :
    @chartAt _ _ _ _ (prodEuclideanChartedSpace (𝕜 := 𝕜)) x =
      ((chartAt (EuclideanSpace 𝕜 (Fin n)) x.1).prod (chartAt (EuclideanSpace 𝕜 (Fin m)) x.2)).trans
        (EuclideanSpace.finAddEquivProd (𝕜 := 𝕜)).symm.toHomeomorph.toOpenPartialHomeomorph :=
  (rfl)

/-- The torus `S¹ × S¹`, charted on `ℝ²` through the product of the circle charts. -/
@[instance_reducible]
noncomputable def torusChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) (Circle × Circle) :=
  prodEuclideanChartedSpace (n := 1) (m := 1)

end TauCeti
