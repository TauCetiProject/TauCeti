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

## References

* Stacks Project, Tag 04GW, for pointed étale neighbourhoods.
* Tau Ceti, `TauCeti.RingTheory.Henselization.SmallModel`, for finite-type-algebra
  essential smallness.
* Taylor Dupuy, Thomas Tucker, and Zhuoran Wang, pcfawd-formalization at `9a20b3f`,
  `StrictHenselizationConstruction.lean`, `PointedEtaleNeighborhood`.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti.StrictHenselization

variable (R : Type u) (Ω : Type v) [CommRing R] [CommRing Ω] [Algebra R Ω]

/-- A pointed étale algebra is a pointed finite-type algebra. -/
private def toPointedFiniteType : Neighbourhood R Ω ⥤
    CostructuredArrow
      (ObjectProperty.ι (fun algebra : CommAlgCat R ↦ Algebra.FiniteType R algebra))
      (CommAlgCat.of R (ULift.{u} Ω)) where
  obj point := by
    let : Algebra.Etale R point.obj.left := (isPointedNeighbourhood_iff R Ω _).mp point.property
    let algebra : FGAlgCat.{max u v} R := ⟨point.obj.left, inferInstance⟩
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
instance neighbourhood_essentiallySmall : EssentiallySmall.{max u v} (Neighbourhood R Ω) := by
  let : EssentiallySmall.{max u v} (FGAlgCat.{max u v} R) := by
    rw [essentiallySmall_iff]
    exact ⟨small_lift.{_, v, u} (Skeleton (FGAlgCat.{max u v} R)), inferInstance⟩
  exact essentiallySmall_of_fully_faithful (toPointedFiniteType R Ω)

end TauCeti.StrictHenselization
