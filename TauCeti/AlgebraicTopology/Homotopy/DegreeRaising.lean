/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.CrossProduct
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Topology.MappingSpace.DoubleLoop

/-!
# The degree-raising map from the double loop space to the loop space

A double loop is a loop in the loop space, so evaluation on the circle gives a map
`S¹ × Ω²X → ΩX` (`TauCeti.BasedTopologicalSpace.evalCircle`). On singular homology with
coefficients in the unit `𝟙` of a monoidal category such as `ModuleCat R`, composing the cross
product with the fundamental class of the circle with the map induced by this evaluation gives the
degree-raising map

`β_* : H_p(Ω²X) ⟶ H_{1+p}(ΩX)`,

natural in the based space `X`.

## Main declarations

* `TauCeti.circleFundamentalClass`: the fundamental class `𝟙 ⟶ H₁(S¹; 𝟙)` of the unit circle in
  `ℝ²`, oriented by the standard basis.
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

private def eastPoint : Sphere1 := ⟨EuclideanSpace.single 0 1, by simp⟩

private def northPoint : Sphere1 := ⟨EuclideanSpace.single 1 1, by simp⟩

private theorem northPoint_mem : northPoint ∈ ({eastPoint}ᶜ ∩ {-eastPoint}ᶜ : Set Sphere1) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := congrArg (fun q : Sphere1 => (q : EuclideanSpace ℝ (Fin 2)) 0) h
    simp [northPoint, eastPoint] at this
  · have := congrArg (fun q : Sphere1 => (q : EuclideanSpace ℝ (Fin 2)) 0) h
    simp [northPoint, eastPoint] at this

/-- **The fundamental class of the circle**: the generator of `H₁(S¹; 𝟙)` determined by the
Mayer–Vietoris isomorphism for the cover by the arcs `S¹ ∖ {(1, 0)}` and `S¹ ∖ {(-1, 0)}`, and the
point `(0, 1)`. -/
def circleFundamentalClass :
    𝟙_ (ModuleCat.{0} R) ⟶
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} R) 1).obj (𝟙_ _)).obj
        (TopCat.of Sphere1) :=
  (singularHomologySphereOneIso (𝟙_ (ModuleCat.{0} R)) (by simp) northPoint_mem).inv

end Class

section Raising

open BasedTopologicalSpace

variable (R : Type) [CommRing R] (X : BasedTopologicalSpace.{0}) (p n : ℕ) (h : 1 + p = n)

/-- The evaluation `S¹ × Ω²X → ΩX` as a morphism of topological spaces. -/
def evalCircleTop :
    TopCat.of Sphere1 ⊗ TopCat.of (X.iteratedLoopSpace 2).carrier ⟶ TopCat.of X.loopSpace.carrier :=
  TopCat.ofHom (evalCircle X eastPoint)

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

variable {X} {Y : BasedTopologicalSpace.{0}}

theorem evalCircleTop_naturality (f : Hom X Y) :
    (𝟙 (TopCat.of Sphere1) ⊗ₘ TopCat.ofHom (f.iteratedLoopSpace 2).toContinuousMap) ≫
        evalCircleTop Y =
      evalCircleTop X ≫ TopCat.ofHom f.loopSpace.toContinuousMap := by
  ext ⟨z, γ⟩
  exact evalCircle_map eastPoint f z γ

/-- **Naturality of the degree-raising map** in the based space `X`: it commutes with the maps
induced on homology by `Ω²f` and `Ωf`. -/
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
