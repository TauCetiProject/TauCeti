/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Basic
public import TauCeti.AlgebraicTopology.Singular.IntervalGenerator
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Geometry.Sphere.Circle
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

For Mathlib's complex unit circle `Circle`, the first homology `H₁(S¹; A)` is identified with `A`
through the standard generator of the homology of `TopCat.sphere 1`.

## Main declarations

* `TauCeti.circleFundamentalClass`: the fundamental class `A ⟶ H₁(S¹; A)` of the unit circle in
  `ℝ²`, the class of the standard loop.
* `TauCeti.hurewicz_circleGenLoop`: the Hurewicz class of the standard loop is minus the
  fundamental class.
* `TauCeti.uliftSphere1FundamentalClass`: the fundamental class of the circle lifted to an arbitrary
  universe, with `TauCeti.uliftSphere1FundamentalClass_comp_map_down` identifying it with
  `TauCeti.circleFundamentalClass` in the smallest universe.
* `Circle.singularHomologyOneIso`: `H₁(S¹; A) ≅ A` for the complex unit circle `Circle`;
  `Circle.singularHomologyOneIso_inv`: its inverse is the standard generator of the sphere.
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

namespace TauCeti

/-! ### The circle in an arbitrary universe -/

section ULift

open scoped Topology.Homotopy

universe w

/-- The standard loop `t ↦ (cos 2πt, sin 2πt)` as a generalized loop in the universe-lifted circle
`ULift.{w} Sphere1`, at the lift of `(1, 0)`. -/
def uliftSphere1GenLoop : Ω^ (Fin 1) (ULift.{w} Sphere1) (ULift.up Sphere1.east) :=
  GenLoop.map ⟨ULift.up, continuous_uliftUp⟩ rfl circleGenLoop

/-- The lifted standard loop is the standard loop followed by `ULift.up`. -/
@[simp]
theorem uliftSphere1GenLoop_apply (t : Fin 1 → unitInterval) :
    uliftSphere1GenLoop.{w} t = ULift.up (circleLoop t) := by
  rw [uliftSphere1GenLoop, GenLoop.map_apply, circleGenLoop_apply, ContinuousMap.coe_mk]

variable {C : Type u} [Category.{v} C] [Abelian C] (A : C)

/-- **The fundamental class of the circle in an arbitrary universe** `w`: the class
`A ⟶ H₁(S¹; A)` of the standard loop on the universe-lifted circle `ULift.{w} Sphere1`, for
coefficients in an abelian category with coproducts indexed by `Type w`. Like
`TauCeti.circleFundamentalClass`, it is minus the Hurewicz class of the standard loop
(`TauCeti.hurewicz_uliftSphere1GenLoop`); in the smallest universe it is carried to
`TauCeti.circleFundamentalClass` by `ULift.down`
(`TauCeti.uliftSphere1FundamentalClass_comp_map_down`). -/
def uliftSphere1FundamentalClass [HasCoproducts.{w} C] :
    A ⟶ ((AlgebraicTopology.singularHomologyFunctor C 1).obj A).obj
      (TopCat.of (ULift.{w} Sphere1)) :=
  -GenLoop.hurewicz A uliftSphere1GenLoop

/-- The Hurewicz class of the lifted standard loop is minus the fundamental class of the lifted
circle. -/
theorem hurewicz_uliftSphere1GenLoop [HasCoproducts.{w} C] :
    GenLoop.hurewicz A uliftSphere1GenLoop.{w} = -uliftSphere1FundamentalClass.{w} A := by
  rw [uliftSphere1FundamentalClass, neg_neg]

/-- **The lifted fundamental class is the fundamental class of the circle**: in the smallest
universe, `ULift.down : ULift Sphere1 → Sphere1` carries `TauCeti.uliftSphere1FundamentalClass` to
`TauCeti.circleFundamentalClass`. -/
@[reassoc (attr := simp)]
theorem uliftSphere1FundamentalClass_comp_map_down [HasCoproducts.{0} C] :
    uliftSphere1FundamentalClass.{0} A ≫ ((AlgebraicTopology.singularHomologyFunctor C 1).obj A).map
        (TopCat.ofHom ⟨ULift.down, continuous_uliftDown⟩) = circleFundamentalClass A := by
  have h : GenLoop.map ⟨ULift.down, continuous_uliftDown⟩ rfl uliftSphere1GenLoop.{0} =
      circleGenLoop :=
    DFunLike.ext _ _ fun t => by
      rw [GenLoop.map_apply, uliftSphere1GenLoop_apply, circleGenLoop_apply, ContinuousMap.coe_mk,
        ULift.down_up]
  rw [uliftSphere1FundamentalClass, Preadditive.neg_comp, ← GenLoop.hurewicz_map A _ rfl, h,
    hurewicz_circleGenLoop, neg_neg]

end ULift

end TauCeti

namespace Circle

open AlgebraicTopology TauCeti

variable {C : Type u} [Category.{v} C] [HasCoproducts.{0} C] [Abelian C] (A : C)

/-- `H₁(S¹; A) ≅ A`, through the standard generator of the homology of `TopCat.sphere 1`
(`TauCeti.reducedSingularHomologyTopCatSphereIso`), transported to the unit circle `Circle`. -/
def singularHomologyOneIso :
    ((singularHomologyFunctor C 1).obj A).obj (TopCat.of Circle) ≅ A :=
  ((singularHomologyFunctor C 1).obj A).mapIso sphereOneIsoCircleUnlifted.symm ≪≫
    ((reducedSingularHomologySuccIso A 0).app _).symm ≪≫ reducedSingularHomologyTopCatSphereIso A 1

/-- **Characteristic equation of `Circle.singularHomologyOneIso`**: its inverse is the standard
generator of the reduced homology of `TopCat.sphere 1`
(`TauCeti.reducedSingularHomologyTopCatSphereIso`), read in unreduced homology and pushed to
`Circle` along `TauCeti.sphereOneIsoCircleUnlifted`. -/
theorem singularHomologyOneIso_inv :
    (singularHomologyOneIso A).inv =
      (reducedSingularHomologyTopCatSphereIso A 1).inv ≫ (reducedSingularHomologyι A 1).app _ ≫
        ((singularHomologyFunctor C 1).obj A).map sphereOneIsoCircleUnlifted.hom := by
  rw [singularHomologyOneIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom,
    reducedSingularHomologySuccIso_hom, Category.assoc]

end Circle
