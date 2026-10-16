/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Circle
public import TauCeti.AlgebraicTopology.Singular.CrossProduct
public import TauCeti.Topology.MappingSpace.Sphere.DoubleLoop

/-!
# The degree-raising map from the double loop space to the loop space

A double loop is a loop in the loop space, so evaluation on the circle gives a map
`S¹ × Ω²X → ΩX` (`TauCeti.BasedTopologicalSpace.evalCircle`). The circle is parametrized by the
standard loop `t ↦ (cos 2πt, sin 2πt)` (`TauCeti.circleLoop`) both in this identification of
double loops with maps from the circle and in the fundamental class
`TauCeti.circleFundamentalClass`, which is the class of that same loop. So `β_*` is oriented by
the standard parametrization of the interval and the circle. On singular homology with
coefficients in the unit `𝟙` of `ModuleCat R`, for a commutative ring `R`, composing the cross
product with the fundamental class of the circle with the map induced by this evaluation gives the
degree-raising map

`β_* : H_p(Ω²X) ⟶ H_{1+p}(ΩX)`,

natural in the based space `X`.

## Main declarations

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

section Raising

open BasedTopologicalSpace

variable (R : Type) [CommRing R] (X : BasedTopologicalSpace.{0}) (p n : ℕ) (h : 1 + p = n)

-- The product in `TopCat` is the type product, so the evaluation map of spaces is a morphism of
-- `TopCat`.
/-- The evaluation `S¹ × Ω²X → ΩX` as a morphism of topological spaces. -/
def evalCircleTop :
    TopCat.of Sphere1 ⊗ TopCat.of (X.iteratedLoopSpace 2).carrier ⟶ TopCat.of X.loopSpace.carrier :=
  TopCat.ofHom (evalCircle X)

/-- The evaluation of spaces `evalCircleTop X` is the bundled evaluation `evalCircle X`. The
definition body is not unfolded outside this module. -/
theorem evalCircleTop_def : evalCircleTop X = TopCat.ofHom (evalCircle X) := by
  rw [evalCircleTop]
  -- the two sides differ only in how the type product is presented as a `TopCat` object
  rfl

/-- **The degree-raising map** `β_* : H_p(Ω²X; 𝟙) ⟶ H_n(ΩX; 𝟙)` for `1 + p = n`: the cross product
with the fundamental class of the circle, followed by the map induced by the evaluation
`S¹ × Ω²X → ΩX`. -/
def degreeRaising :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) p).obj (𝟙_ _)).obj
        (TopCat.of (X.iteratedLoopSpace 2).carrier) ⟶
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).obj (𝟙_ _)).obj
        (TopCat.of X.loopSpace.carrier) :=
  (λ_ _).inv ≫ (circleFundamentalClass (𝟙_ (ModuleCat.{0} R)) ▷ _) ≫
    TopCat.singularHomologyCross (C := ModuleCat.{0} R) (TopCat.of Sphere1)
      (TopCat.of (X.iteratedLoopSpace 2).carrier) (𝟙_ _) (𝟙_ _) 1 p n h ≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).map (λ_ (𝟙_ _)).hom).app _ ≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).obj (𝟙_ _)).map
      (evalCircleTop X)

/-- **Characteristic equation of the degree-raising map**: `β_*` is the left unitor inverse, the
fundamental class of the circle, the homology cross product, the coefficient unitor, and the map
induced by the evaluation `S¹ × Ω²X → ΩX`. The definition body is not unfolded outside this
module, so this equation is how consumers reach the composite. -/
theorem degreeRaising_def :
    degreeRaising R X p n h =
      (λ_ _).inv ≫ (circleFundamentalClass (𝟙_ (ModuleCat.{0} R)) ▷ _) ≫
        TopCat.singularHomologyCross (C := ModuleCat.{0} R) (TopCat.of Sphere1)
          (TopCat.of (X.iteratedLoopSpace 2).carrier) (𝟙_ _) (𝟙_ _) 1 p n h ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).map
          (λ_ (𝟙_ _)).hom).app _ ≫
        ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) n).obj (𝟙_ _)).map
          (evalCircleTop X) := by
  rw [degreeRaising]

variable {X} {Y : BasedTopologicalSpace.{0}}

/-- Naturality of the evaluation `S¹ × Ω²X → ΩX` as a square of morphisms of topological spaces. -/
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
  rw [degreeRaising_def, degreeRaising_def]
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
