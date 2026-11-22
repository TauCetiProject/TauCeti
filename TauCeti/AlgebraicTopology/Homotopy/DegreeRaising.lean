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
double loops with maps from the circle and in the fundamental class of the circle, which is the
class of that same loop. So `β_*` is oriented by the standard parametrization of the interval and
the circle.

Let `X` be a based space in a universe `u`, `R` a commutative ring in the same universe and `M`
an `R`-module, also in `u`. The circle is lifted to `ULift.{u} Sphere1`, so that it lives in the
universe of `X`, with fundamental class `TauCeti.uliftSphere1FundamentalClass`. On singular homology
with coefficients in `M`, composing the cross product with this fundamental class (with
coefficients in the unit `R` of `ModuleCat R`), the unitor `R ⊗ M ≅ M` and the map induced by the
evaluation gives the degree-raising map

`β_* : H_p(Ω²X; M) ⟶ H_{1+p}(ΩX; M)`,

natural in the based space `X` and in the coefficient module `M`. In the smallest universe the
lift is invisible: `β_*` is the same composite through the circle `Sphere1` itself and its
fundamental class `TauCeti.circleFundamentalClass`
(`TauCeti.map_comp_degreeRaising_eq_evalCircle`).

## Main declarations

* `TauCeti.degreeRaising`: the degree-raising map `H_p(Ω²X; M) ⟶ H_n(ΩX; M)` for `1 + p = n`.
* `TauCeti.map_comp_degreeRaising`: on the class `ℓ_* c` of a family `ℓ : A → Ω²X` of double
  loops, `β_*` is the image of `[S¹] × c` under the evaluation `S¹ × A → ΩX`,
  `(z, a) ↦ ℓ a (z)`.
* `TauCeti.map_comp_degreeRaising_eq_evalCircle`: the same formula in the smallest universe, with
  the circle `Sphere1` and `TauCeti.circleFundamentalClass`.
* `TauCeti.degreeRaising_naturality`: its naturality in `X`.
* `TauCeti.degreeRaising_coefficient_naturality`: its naturality in the coefficient module.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.2.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Metric

namespace TauCeti

universe u

section Raising

open BasedTopologicalSpace AlgebraicTopology

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (X : BasedTopologicalSpace.{u})
  (p n : ℕ) (h : 1 + p = n)

-- The product in `TopCat` is the type product, so the evaluation map of spaces is a morphism of
-- `TopCat`.
/-- The evaluation `S¹ × Ω²X → ΩX` as a morphism of topological spaces, with the circle lifted to
the universe of `X`. -/
def evalCircleTop :
    TopCat.of (ULift.{u} Sphere1) ⊗ TopCat.of (X.iteratedLoopSpace 2).carrier ⟶
      TopCat.of X.loopSpace.carrier :=
  TopCat.ofHom ((evalCircle X).comp
    (ContinuousMap.prodMap ⟨ULift.down, continuous_uliftDown⟩ (ContinuousMap.id _)))

/-- The evaluation of spaces `evalCircleTop X` evaluates a double loop at the point of the circle
underlying a point of the lifted circle. -/
theorem evalCircleTop_apply (z : ULift.{u} Sphere1) (γ : (X.iteratedLoopSpace 2).carrier) :
    evalCircleTop X (z, γ) = evalCircle X (z.down, γ) := by
  rw [evalCircleTop]
  -- the morphism of `TopCat` evaluates as the underlying composite of continuous maps
  rfl

/-- **The degree-raising map** `β_* : H_p(Ω²X; M) ⟶ H_n(ΩX; M)` for `1 + p = n`: the cross product
with the fundamental class of the circle, followed by the unitor `R ⊗ M ≅ M` on coefficients and the
map induced by the evaluation `S¹ × Ω²X → ΩX`. -/
def degreeRaising :
    ((singularHomologyFunctor (ModuleCat.{u} R) p).obj M).obj
        (TopCat.of (X.iteratedLoopSpace 2).carrier) ⟶
      ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).obj
        (TopCat.of X.loopSpace.carrier) :=
  (λ_ _).inv ≫ (uliftSphere1FundamentalClass.{u} (𝟙_ (ModuleCat.{u} R)) ▷ _) ≫
    TopCat.singularHomologyCross (TopCat.of (ULift.{u} Sphere1))
      (TopCat.of (X.iteratedLoopSpace 2).carrier) (𝟙_ _) M 1 p n h ≫
    ((singularHomologyFunctor (ModuleCat.{u} R) n).map (λ_ M).hom).app _ ≫
    ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (evalCircleTop X)

/-- **Characteristic equation of the degree-raising map**: `β_*` is the left unitor inverse, the
fundamental class of the circle, the homology cross product, the coefficient unitor, and the map
induced by the evaluation `S¹ × Ω²X → ΩX`. The definition body is not unfolded outside this
module, so this equation is how consumers reach the composite. -/
theorem degreeRaising_def :
    degreeRaising M X p n h =
      (λ_ _).inv ≫ (uliftSphere1FundamentalClass.{u} (𝟙_ (ModuleCat.{u} R)) ▷ _) ≫
        TopCat.singularHomologyCross (TopCat.of (ULift.{u} Sphere1))
          (TopCat.of (X.iteratedLoopSpace 2).carrier) (𝟙_ _) M 1 p n h ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).map (λ_ M).hom).app _ ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map (evalCircleTop X) := by
  rw [degreeRaising]

/-- **The degree-raising map on the class of a family of double loops.** For a family
`ℓ : A → Ω²X`, the degree-raising map sends `ℓ_* c` to the image of `[S¹] × c` under the map
`S¹ × A → ΩX`, `(z, a) ↦ ℓ a (z)`. -/
@[reassoc]
theorem map_comp_degreeRaising {A : TopCat.{u}}
    (ℓ : A ⟶ TopCat.of (X.iteratedLoopSpace 2).carrier) :
    ((singularHomologyFunctor (ModuleCat.{u} R) p).obj M).map ℓ ≫ degreeRaising M X p n h =
      (λ_ _).inv ≫ (uliftSphere1FundamentalClass.{u} (𝟙_ (ModuleCat.{u} R)) ▷ _) ≫
        TopCat.singularHomologyCross (TopCat.of (ULift.{u} Sphere1)) A (𝟙_ _) M 1 p n h ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).map (λ_ M).hom).app _ ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          ((𝟙 (TopCat.of (ULift.{u} Sphere1)) ⊗ₘ ℓ) ≫ evalCircleTop X) := by
  rw [degreeRaising_def]
  have hn := TopCat.singularHomologyCross_naturality (C := ModuleCat.{u} R)
    (𝟙 (TopCat.of (ULift.{u} Sphere1))) ℓ (𝟙_ _) M 1 p n h
  rw [CategoryTheory.Functor.map_id, id_tensorHom] at hn
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, reassoc_of% hn,
    NatTrans.naturality_assoc, CategoryTheory.Functor.map_comp]

variable {X} {Y : BasedTopologicalSpace.{u}}

/-- Naturality of the evaluation `S¹ × Ω²X → ΩX` as a square of morphisms of topological spaces. -/
-- Both sides are continuous maps out of the type product, which is the `TopCat` product; the
-- equality is checked on points.
theorem evalCircleTop_naturality (f : Hom X Y) :
    (𝟙 (TopCat.of (ULift.{u} Sphere1)) ⊗ₘ TopCat.ofHom (f.iteratedLoopSpace 2).toContinuousMap) ≫
        evalCircleTop Y =
      evalCircleTop X ≫ TopCat.ofHom f.loopSpace.toContinuousMap := by
  ext ⟨z, γ⟩
  exact (evalCircleTop_apply Y z _).trans
    ((evalCircle_map f z.down γ).trans (congrArg f.loopSpace (evalCircleTop_apply X z γ).symm))

/-- **Naturality of the degree-raising map** in the based space `X`: it commutes with the maps
induced on homology by `Ω²f` and `Ωf`. -/
@[reassoc]
theorem degreeRaising_naturality (f : Hom X Y) :
    ((singularHomologyFunctor (ModuleCat.{u} R) p).obj M).map
          (TopCat.ofHom (f.iteratedLoopSpace 2).toContinuousMap) ≫
        degreeRaising M Y p n h =
      degreeRaising M X p n h ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).obj M).map
          (TopCat.ofHom f.loopSpace.toContinuousMap) := by
  rw [map_comp_degreeRaising, evalCircleTop_naturality, degreeRaising_def,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

variable {M} {M' : ModuleCat.{u} R}

/-- **Naturality of the degree-raising map** in the coefficient module: it commutes with the maps
induced on homology by a linear map `φ : M ⟶ M'`. -/
@[reassoc]
theorem degreeRaising_coefficient_naturality (X : BasedTopologicalSpace.{u}) (φ : M ⟶ M') :
    ((singularHomologyFunctor (ModuleCat.{u} R) p).map φ).app
          (TopCat.of (X.iteratedLoopSpace 2).carrier) ≫
        degreeRaising M' X p n h =
      degreeRaising M X p n h ≫
        ((singularHomologyFunctor (ModuleCat.{u} R) n).map φ).app
          (TopCat.of X.loopSpace.carrier) := by
  have hc := TopCat.singularHomologyCross_coefficient_naturality (C := ModuleCat.{u} R)
    (TopCat.of (ULift.{u} Sphere1)) (TopCat.of (X.iteratedLoopSpace 2).carrier)
    (𝟙 (𝟙_ (ModuleCat.{u} R))) φ 1 p n h
  rw [CategoryTheory.Functor.map_id, NatTrans.id_app, id_tensorHom] at hc
  rw [degreeRaising_def, degreeRaising_def]
  -- Move `φ` past the inverse unitor and the whiskered fundamental class, into the coefficient
  -- slot of the cross product.
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
  -- Naturality of the cross product in the coefficients carries `𝟙 ⊗ φ` to its output.
  rw [reassoc_of% hc]
  -- Naturality of the unitor: `(𝟙 ⊗ φ) ≫ (λ_ M').hom = (λ_ M).hom ≫ φ`, applied inside the
  -- homology functor.
  rw [← NatTrans.comp_app_assoc, ← CategoryTheory.Functor.map_comp, id_tensorHom,
    leftUnitor_naturality, CategoryTheory.Functor.map_comp, NatTrans.comp_app_assoc]
  -- The map induced by `φ` commutes with the map induced by the evaluation.
  rw [← NatTrans.naturality]
  simp only [Category.assoc]

end Raising

section UniverseZero

open BasedTopologicalSpace AlgebraicTopology

variable {R : Type} [CommRing R] (M : ModuleCat.{0} R) (X : BasedTopologicalSpace.{0})
  (p n : ℕ) (h : 1 + p = n)

/-- **The degree-raising map in the smallest universe**, through the circle `Sphere1` itself: on
the class `ℓ_* c` of a family `ℓ : A → Ω²X` of double loops, `β_*` is the image of `[S¹] × c`
under `evalCircle X ∘ (id × ℓ) : S¹ × A → ΩX`, `(z, a) ↦ ℓ a (z)`, with `[S¹]` the fundamental class
`TauCeti.circleFundamentalClass` of `Sphere1`. -/
@[reassoc]
theorem map_comp_degreeRaising_eq_evalCircle {A : TopCat.{0}}
    (ℓ : A ⟶ TopCat.of (X.iteratedLoopSpace 2).carrier) :
    ((singularHomologyFunctor (ModuleCat.{0} R) p).obj M).map ℓ ≫ degreeRaising M X p n h =
      (λ_ _).inv ≫ (circleFundamentalClass (𝟙_ (ModuleCat.{0} R)) ▷ _) ≫
        TopCat.singularHomologyCross (TopCat.of Sphere1) A (𝟙_ _) M 1 p n h ≫
        ((singularHomologyFunctor (ModuleCat.{0} R) n).map (λ_ M).hom).app _ ≫
        ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).map
          (TopCat.ofHom ((evalCircle X).comp ((ContinuousMap.id Sphere1).prodMap ℓ.hom)) :
            TopCat.of Sphere1 ⊗ A ⟶ TopCat.of X.loopSpace.carrier) := by
  -- The lifted circle maps to `Sphere1` by `ULift.down`, which carries the lifted fundamental
  -- class to the fundamental class, and the evaluation on the lifted circle factors through it.
  let d : TopCat.of (ULift.{0} Sphere1) ⟶ TopCat.of Sphere1 :=
    TopCat.ofHom ⟨ULift.down, continuous_uliftDown⟩
  have he : ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).map
      ((𝟙 (TopCat.of (ULift.{0} Sphere1)) ⊗ₘ ℓ) ≫ evalCircleTop X) =
      ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).map (d ⊗ₘ 𝟙 A) ≫
        ((singularHomologyFunctor (ModuleCat.{0} R) n).obj M).map
          (TopCat.ofHom ((evalCircle X).comp ((ContinuousMap.id Sphere1).prodMap ℓ.hom)) :
            TopCat.of Sphere1 ⊗ A ⟶ TopCat.of X.loopSpace.carrier) := by
    -- `Functor.map_comp` is applied as a term: the evaluation on `Sphere1` is typed through the
    -- type product, which is the `TopCat` product only up to unfolding.
    refine Eq.trans ?_ (CategoryTheory.Functor.map_comp _ (d ⊗ₘ 𝟙 A) _)
    exact congrArg _ (TopCat.ext fun x ↦ evalCircleTop_apply X x.1 (ℓ x.2))
  have hn := TopCat.singularHomologyCross_naturality (C := ModuleCat.{0} R) d (𝟙 A) (𝟙_ _) M 1 p
    n h
  rw [CategoryTheory.Functor.map_id, tensorHom_id] at hn
  rw [map_comp_degreeRaising, he, ← NatTrans.naturality_assoc, ← reassoc_of% hn,
    ← comp_whiskerRight_assoc, uliftSphere1FundamentalClass_comp_map_down]

end UniverseZero

end TauCeti
