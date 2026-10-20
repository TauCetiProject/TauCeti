/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StrictHenselization.Neighbourhood
public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Essential smallness of pointed étale neighbourhoods

Retaining the point gives a fully faithful embedding into the category of
finite-type algebras equipped with a map to the chosen commutative algebra.
-/

public section

open CategoryTheory

universe u

namespace TauCeti.StrictHenselization

variable (R Ω : Type u) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- A pointed étale algebra is a pointed finite-type algebra. -/
private def toPointedFiniteType : Neighbourhood R Ω ⥤
    CostructuredArrow
      (ObjectProperty.ι (fun algebra : CommAlgCat R ↦ Algebra.FiniteType R algebra))
      (CommAlgCat.of R Ω) where
  obj point := by
    let : Algebra.Etale R point.obj.left := (isPointedNeighbourhood_iff R Ω _).mp point.property
    let algebra : FGAlgCat.{u} R := ⟨point.obj.left, inferInstance⟩
    exact CostructuredArrow.mk (Y := algebra) point.obj.hom
  map morphism := CostructuredArrow.homMk (ObjectProperty.homMk morphism.hom.left) morphism.hom.w

/-- Distinct pointed-neighbourhood morphisms remain distinct after forgetting étaleness. -/
private instance : (toPointedFiniteType R Ω).Faithful where
  map_injective equality := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact congrArg (fun morphism ↦ morphism.left.hom) equality

/-- Every pointed finite-type morphism between étale objects is a neighbourhood morphism. -/
private instance : (toPointedFiniteType R Ω).Full where
  map_surjective morphism := by
    refine ⟨ObjectProperty.homMk (Over.homMk morphism.left.hom morphism.w), ?_⟩
    apply CostructuredArrow.ext
    apply ObjectProperty.hom_ext
    rfl

/-- Pointed étale neighbourhoods have a small model. -/
instance neighbourhood_essentiallySmall : EssentiallySmall.{u} (Neighbourhood R Ω) :=
  essentiallySmall_of_fully_faithful (toPointedFiniteType R Ω)

end TauCeti.StrictHenselization
