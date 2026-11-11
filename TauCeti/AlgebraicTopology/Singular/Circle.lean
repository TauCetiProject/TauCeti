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

* `TauCeti.circlePair`: the circle with its basepoint, as a topological pair.
* `TauCeti.circleLoopPairHom`: the standard loop as a map of pairs `(I¹, ∂I¹) ⟶ (S¹, {(1, 0)})`.
* `TauCeti.circleFundamentalClass`: the fundamental class `A ⟶ H₁(S¹; A)` of the unit circle in
  `ℝ²`, the class of the standard loop.
* `TauCeti.circleGenLoop`: the standard loop as a generalized loop at `(1, 0)`.
* `TauCeti.hurewicz_circleGenLoop`: its Hurewicz class is minus the fundamental class.
-/

public section

noncomputable section

open CategoryTheory Limits Metric
open scoped Topology.Homotopy

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

/-- The standard loop `t ↦ (cos 2πt, sin 2πt)` as a generalized loop `I¹ → S¹` at `(1, 0)`. -/
def circleGenLoop : Ω^ (Fin 1) Sphere1 Sphere1.east :=
  ⟨circleLoop, fun t ht => (circleLoop_eq_east_iff t).2 ht⟩

@[simp]
theorem circleGenLoop_apply (t : Fin 1 → unitInterval) : circleGenLoop t = circleLoop t :=
  (rfl)

/-- The map of pairs of the generalized loop `TauCeti.circleGenLoop` is the standard loop pair map
`TauCeti.circleLoopPairHom`. -/
theorem toCubeBoundaryPairHom_circleGenLoop :
    GenLoop.toCubeBoundaryPairHom circleGenLoop = circleLoopPairHom := by
  apply TopPair.hom_ext_of_fst
  ext t
  exact (GenLoop.toCubeBoundaryPairHom_fst_apply circleGenLoop t).trans
    (circleLoopPairHom_fst_apply t).symm

/-- **The Hurewicz class of the standard loop is minus the fundamental class of the circle.** The
Hurewicz map reads the loop through the generator of `H₁(I¹, ∂I¹; A)`, the class of the singular
simplex from `1` to `0`, and the fundamental class reads it through the simplex from `0` to `1`. -/
theorem hurewicz_circleGenLoop :
    GenLoop.hurewicz A circleGenLoop = -circleFundamentalClass A := by
  rw [← cancel_mono (singularHomologyIsoOfSubsetSingleton A 0 Sphere1.east).hom,
    GenLoop.hurewicz_comp_singularHomologyIsoOfSubsetSingleton_hom,
    singularHomologyCubeBoundaryPairIso_one_inv, toCubeBoundaryPairHom_circleGenLoop,
    circleFundamentalClass_def, Preadditive.neg_comp, Preadditive.neg_comp, Category.assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

end TauCeti
