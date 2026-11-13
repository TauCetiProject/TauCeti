/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Basic
public import TauCeti.AlgebraicTopology.Singular.IntervalGenerator
public import TauCeti.Topology.Sphere.StandardCircle

/-!
# The fundamental class of the circle

The circle `S¹ ⊆ ℝ²`, with the basepoint `(1, 0)`, is oriented by the standard loop
`t ↦ (cos 2πt, sin 2πt)` (`TauCeti.circleLoop`). Its fundamental class in singular homology with
coefficients in an object `A` of an abelian category with coproducts is the class of that loop.

The standard loop is also a generalized loop `TauCeti.circleGenLoop` at `(1, 0)`. Its Hurewicz
class is minus the fundamental class (`TauCeti.hurewicz_circleGenLoop`): the Hurewicz map reads
a loop through the generator of `H₁(I¹, ∂I¹; A)`, which is the class of the singular simplex running
from `1` to `0` (`TauCeti.singularHomologyCubeBoundaryPairIso_one_inv`), while the fundamental
class reads the standard loop along the simplex running from `0` to `1`.

## Main declarations

* `TauCeti.circleFundamentalClass`: the fundamental class `A ⟶ H₁(S¹; A)` of the unit circle in
  `ℝ²`, the class of the standard loop.
* `TauCeti.hurewicz_circleGenLoop`: the Hurewicz class of the standard loop is minus the
  fundamental class.
-/

public section

noncomputable section

open CategoryTheory Limits Metric

namespace TauCeti

universe u v

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C] (A : C)

/-- **The fundamental class of the circle**, with coefficients in an object `A` of an abelian
category with coproducts: the class `A ⟶ H₁(S¹; A)` of the standard loop `t ↦ (cos 2πt, sin 2πt)`.
It is the image of the relative class of the standard `1`-simplex of the interval `I¹` under the
loop, followed by the inverse of `H₁(S¹; A) ≅ H₁(S¹, {(1, 0)}; A)`
(`TauCeti.singularHomologyIsoOfSubsetSingleton`). The circle is oriented by this
parametrization, which is also the one with which double loops are read as maps from the circle in
`TauCeti.BasedTopologicalSpace.loopSpace2Homeomorph`. -/
def circleFundamentalClass :
    A ⟶ ((AlgebraicTopology.singularHomologyFunctor C 1).obj A).obj (TopCat.of Sphere1) :=
  cubeRelClass A ≫
    TopPair.singularHomologyMap (GenLoop.toCubeBoundaryPairHom circleGenLoop) A 1 ≫
      (singularHomologyIsoOfSubsetSingleton A 0 Sphere1.east).inv

/-- **Characteristic equation of the fundamental class of the circle**: it is the relative class of
the standard `1`-simplex of the interval, pushed along the standard loop as a map of pairs, followed
by the inverse of `H₁(S¹; A) ≅ H₁(S¹, {(1, 0)}; A)`. The definition body is not unfolded outside
this module, so this equation is how consumers reach the composite. -/
theorem circleFundamentalClass_def :
    circleFundamentalClass A =
      cubeRelClass A ≫
        TopPair.singularHomologyMap (GenLoop.toCubeBoundaryPairHom circleGenLoop) A 1 ≫
          (singularHomologyIsoOfSubsetSingleton A 0 Sphere1.east).inv := by
  rw [circleFundamentalClass]

/-- **The Hurewicz class of the standard loop is minus the fundamental class of the circle.** The
Hurewicz map reads the loop through the generator of `H₁(I¹, ∂I¹; A)`, the class of the singular
simplex from `1` to `0`, and the fundamental class reads it through the simplex from `0` to `1`. -/
theorem hurewicz_circleGenLoop :
    GenLoop.hurewicz A circleGenLoop = -circleFundamentalClass A := by
  rw [← cancel_mono (singularHomologyIsoOfSubsetSingleton A 0 Sphere1.east).hom,
    GenLoop.hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom,
    singularHomologyCubeBoundaryPairIso_one_inv, circleFundamentalClass_def, Preadditive.neg_comp,
    Preadditive.neg_comp, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end TauCeti
