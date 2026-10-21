/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.IntervalGenerator
public import TauCeti.Topology.Sphere.StandardCircle

/-!
# The fundamental class of the circle

The circle `S¹ ⊆ ℝ²`, with the basepoint `(1, 0)`, is oriented by the standard loop
`t ↦ (cos 2πt, sin 2πt)` (`TauCeti.circleLoop`). Its fundamental class in singular homology with
coefficients in an object `A` of an abelian category with coproducts is the class of that loop.

## Main declarations

* `TauCeti.circlePair`: the circle with its basepoint, as a topological pair.
* `TauCeti.circleLoopPairHom`: the standard loop as a map of pairs `(I¹, ∂I¹) ⟶ (S¹, {(1, 0)})`.
* `TauCeti.circleFundamentalClass`: the fundamental class `A ⟶ H₁(S¹; A)` of the unit circle in
  `ℝ²`, the class of the standard loop.
-/

public section

noncomputable section

open CategoryTheory Limits Metric

namespace TauCeti

/-- The circle `S¹` with the basepoint `(1, 0)`, as a topological pair. -/
abbrev circlePair : TopPair.{0} := TopPair.ofSubset (X := TopCat.of Sphere1) {Sphere1.east}

/-- The standard loop `t ↦ (cos 2πt, sin 2πt)` as a map of pairs
`(I¹, ∂I¹) ⟶ (S¹, {(1, 0)})`. -/
def circleLoopPairHom : cubeBoundaryPair.{0} 1 ⟶ circlePair :=
  TopPair.ofSubsetMap
    (TopCat.ofHom (circleLoop.comp ⟨ULift.down, continuous_uliftDown⟩))
    fun t ht => Set.mem_singleton_iff.2 ((circleLoop_eq_east_iff t.down).2 ht)

/-- The standard loop pair map takes a point of the cube to its image under the standard loop. -/
@[simp]
theorem circleLoopPairHom_fst_apply (t : (cubeBoundaryPair.{0} 1).fst) :
    TopPair.Hom.fst circleLoopPairHom t = circleLoop t.down := by
  rw [circleLoopPairHom]
  exact TopPair.ofSubsetMap_fst_apply _ _ t

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
  cubeRelClass A ≫ TopPair.singularHomologyMap circleLoopPairHom A 1 ≫
    (singularHomologyIsoOfSubsetSingleton A 0 Sphere1.east).inv

/-- **Characteristic equation of the fundamental class of the circle**: it is the relative class of
the standard `1`-simplex of the interval, pushed along the standard loop as a map of pairs, followed
by the inverse of `H₁(S¹; A) ≅ H₁(S¹, {(1, 0)}; A)`. The definition body is not unfolded outside
this module, so this equation is how consumers reach the composite. -/
theorem circleFundamentalClass_def :
    circleFundamentalClass A =
      cubeRelClass A ≫ TopPair.singularHomologyMap circleLoopPairHom A 1 ≫
        (singularHomologyIsoOfSubsetSingleton A 0 Sphere1.east).inv := by
  rw [circleFundamentalClass]

end TauCeti
