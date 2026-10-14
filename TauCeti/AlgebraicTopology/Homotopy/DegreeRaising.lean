/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Contractible
public import TauCeti.AlgebraicTopology.Singular.CrossProduct
public import TauCeti.AlgebraicTopology.Singular.IntervalGenerator
public import TauCeti.AlgebraicTopology.Singular.ReducedRelative
public import TauCeti.Topology.MappingSpace.Sphere.DoubleLoop

/-!
# The degree-raising map from the double loop space to the loop space

A double loop is a loop in the loop space, so evaluation on the circle gives a map
`S¹ × Ω²X → ΩX` (`TauCeti.BasedTopologicalSpace.evalCircle`). The circle is parametrized by the
standard loop `t ↦ (cos 2πt, sin 2πt)` (`TauCeti.circleLoop`) both in this identification of double
loops with maps from the circle and in the fundamental class below, which is the class of that same
loop. So `β_*` is oriented by the standard parametrization of the interval and the circle. On singular homology with
coefficients in the unit `𝟙` of a monoidal category such as `ModuleCat R`, composing the cross
product with the fundamental class of the circle with the map induced by this evaluation gives the
degree-raising map

`β_* : H_p(Ω²X) ⟶ H_{1+p}(ΩX)`,

natural in the based space `X`.

## Main declarations

* `TauCeti.circleFundamentalClass`: the fundamental class `𝟙 ⟶ H₁(S¹; 𝟙)` of the unit circle in
  `ℝ²`, the class of the standard loop.
* `TauCeti.degreeRaising`: the degree-raising map `H_p(Ω²X; 𝟙) ⟶ H_n(ΩX; 𝟙)` for `1 + p = n`.
* `TauCeti.degreeRaising_naturality`: its naturality in `X`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.2.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Metric

namespace TauCeti

section Class

variable (R : Type) [CommRing R]

/-- The circle `S¹` with the basepoint `(1, 0)`, as a topological pair. -/
abbrev circlePair : TopPair.{0} := TopPair.ofSubset (X := TopCat.of Sphere1) {Sphere1.east}

/-- The standard loop `t ↦ (cos 2πt, sin 2πt)` as a map of pairs
`(I¹, ∂I¹) ⟶ (S¹, {(1, 0)})`. -/
def circleLoopPairHom : cubeBoundaryPair.{0} 1 ⟶ circlePair :=
  TopPair.ofSubsetMap
    (TopCat.ofHom (circleLoop.comp ⟨ULift.down, continuous_uliftDown⟩))
    fun t ht => Set.mem_singleton_iff.2 ((circleLoop_eq_east_iff t.down).2 ht)

/-- The inclusion of the circle into the pair `(S¹, {(1, 0)})` induces an isomorphism on first
homology, since the point is contractible. -/
instance isIso_circlePair_singularHomologyπ :
    IsIso (circlePair.singularHomologyπ (𝟙_ (ModuleCat.{0} R)) 1) :=
  haveI : ContractibleSpace circlePair.snd :=
    inferInstanceAs (ContractibleSpace ↥({Sphere1.east} : Set Sphere1))
  TopPair.isIso_singularHomologyπ (P := circlePair) (𝟙_ (ModuleCat.{0} R)) (k := 0)
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace _ circlePair.snd 1)
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace _ circlePair.snd 0)

/-- **The fundamental class of the circle**: the class of the standard loop
`t ↦ (cos 2πt, sin 2πt)`. It is the image of the relative class of the standard `1`-simplex of the
interval `I¹` under the loop, followed by the inverse of `H₁(S¹) ≅ H₁(S¹, {(1, 0)})`. The circle
is oriented by this parametrization, which is also the one with which double loops are read as
maps from the circle in `TauCeti.BasedTopologicalSpace.loopSpace2Homeomorph`. -/
def circleFundamentalClass :
    𝟙_ (ModuleCat.{0} R) ⟶
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) 1).obj (𝟙_ _)).obj
        (TopCat.of Sphere1) :=
  cubeRelClass (𝟙_ (ModuleCat.{0} R)) ≫
    TopPair.singularHomologyMap circleLoopPairHom (𝟙_ (ModuleCat.{0} R)) 1 ≫
      @inv _ _ _ _ (circlePair.singularHomologyπ (𝟙_ (ModuleCat.{0} R)) 1)
        (isIso_circlePair_singularHomologyπ R)

end Class

section Raising

open BasedTopologicalSpace

variable (R : Type) [CommRing R] (X : BasedTopologicalSpace.{0}) (p n : ℕ) (h : 1 + p = n)

-- The product in `TopCat` is the type product, so the evaluation map of spaces is a morphism of
-- `TopCat`.
/-- The evaluation `S¹ × Ω²X → ΩX` as a morphism of topological spaces. -/
def evalCircleTop :
    TopCat.of Sphere1 ⊗ TopCat.of (X.iteratedLoopSpace 2).carrier ⟶ TopCat.of X.loopSpace.carrier :=
  TopCat.ofHom (evalCircle X)

/-- **The degree-raising map** `β_* : H_p(Ω²X; 𝟙) ⟶ H_n(ΩX; 𝟙)` for `1 + p = n`: the cross product
with the fundamental class of the circle, followed by the map induced by the evaluation
`S¹ × Ω²X → ΩX`. -/
def degreeRaising :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) p).obj (𝟙_ _)).obj
        (TopCat.of (X.iteratedLoopSpace 2).carrier) ⟶
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).obj (𝟙_ _)).obj
        (TopCat.of X.loopSpace.carrier) :=
  (λ_ _).inv ≫ (circleFundamentalClass R ▷ _) ≫
    TopCat.singularHomologyCross (C := ModuleCat.{0} R) (TopCat.of Sphere1)
      (TopCat.of (X.iteratedLoopSpace 2).carrier) (𝟙_ _) (𝟙_ _) 1 p n h ≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).map (λ_ (𝟙_ _)).hom).app _ ≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).obj (𝟙_ _)).map
      (evalCircleTop X)

/-- The degree-raising map is the left unitor inverse, the fundamental class of the circle, the
homology cross product, the coefficient unitor, and the map induced by the evaluation. -/
theorem degreeRaising_def :
    degreeRaising R X p n h =
      (λ_ _).inv ≫ (circleFundamentalClass R ▷ _) ≫
        TopCat.singularHomologyCross (C := ModuleCat.{0} R) (TopCat.of Sphere1)
          (TopCat.of (X.iteratedLoopSpace 2).carrier) (𝟙_ _) (𝟙_ _) 1 p n h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).map
          (λ_ (𝟙_ _)).hom).app _ ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).obj (𝟙_ _)).map
          (evalCircleTop X) := by
  rw [degreeRaising]

variable {X} {Y : BasedTopologicalSpace.{0}}

-- Both sides are continuous maps out of the type product, which is the `TopCat` product; the
-- equality is checked on points.
theorem evalCircleTop_naturality (f : Hom X Y) :
    (𝟙 (TopCat.of Sphere1) ⊗ₘ TopCat.ofHom (f.iteratedLoopSpace 2).toContinuousMap) ≫
        evalCircleTop Y =
      evalCircleTop X ≫ TopCat.ofHom f.loopSpace.toContinuousMap := by
  ext ⟨z, γ⟩
  exact evalCircle_map f z γ

/-- **Naturality of the degree-raising map** in the based space `X`: it commutes with the maps
induced on homology by `Ω²f` and `Ωf`. -/
@[reassoc]
theorem degreeRaising_naturality (f : Hom X Y) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) p).obj (𝟙_ _)).map
          (TopCat.ofHom (f.iteratedLoopSpace 2).toContinuousMap) ≫
        degreeRaising R Y p n h =
      degreeRaising R X p n h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).obj (𝟙_ _)).map
          (TopCat.ofHom f.loopSpace.toContinuousMap) := by
  rw [degreeRaising, degreeRaising]
  simp only [Category.assoc]
  have hn := TopCat.singularHomologyCross_naturality (C := ModuleCat.{0} R)
    (𝟙 (TopCat.of Sphere1)) (TopCat.ofHom (f.iteratedLoopSpace 2).toContinuousMap)
    (𝟙_ _) (𝟙_ _) 1 p n h
  rw [CategoryTheory.Functor.map_id, id_tensorHom] at hn
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, reassoc_of% hn]
  have nat := ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).map
    (λ_ (𝟙_ (ModuleCat.{0} R))).hom).naturality
    (𝟙 (TopCat.of Sphere1) ⊗ₘ TopCat.ofHom (f.iteratedLoopSpace 2).toContinuousMap)
  have hsuf :
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).obj (𝟙_ _ ⊗ 𝟙_ _)).map
          (𝟙 (TopCat.of Sphere1) ⊗ₘ TopCat.ofHom (f.iteratedLoopSpace 2).toContinuousMap) ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).map
          (λ_ (𝟙_ (ModuleCat.{0} R))).hom).app _ ≫
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).obj (𝟙_ _)).map
            (evalCircleTop Y) =
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).map
          (λ_ (𝟙_ (ModuleCat.{0} R))).hom).app _ ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).obj (𝟙_ _)).map
            (evalCircleTop X) ≫
          ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).obj (𝟙_ _)).map
            (TopCat.ofHom f.loopSpace.toContinuousMap) := by
    rw [reassoc_of% nat, ← CategoryTheory.Functor.map_comp, evalCircleTop_naturality,
      CategoryTheory.Functor.map_comp]
  rw [hsuf]

end Raising

end TauCeti
