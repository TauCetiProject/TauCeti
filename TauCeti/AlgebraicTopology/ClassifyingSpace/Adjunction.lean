/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import TauCeti.AlgebraicTopology.ClassifyingSpace.HomotopyFunctor

/-!
# The fundamental group is left adjoint to the classifying space

Let `𝒞` be the full subcategory of the pointed homotopy category on the path-connected Hausdorff
CW complexes, with an arbitrary base point
(`TauCeti.PointedHomotopyCat.isPathConnectedCWComplex`). Milnor's classifying space lands in `𝒞`,
so the classifying-space functor restricts to `TauCeti.classifyingSpaceCWFunctor : GrpCat ⥤ 𝒞`.
The fundamental group, restricted to `𝒞`, is its left adjoint
(`TauCeti.fundamentalGroupClassifyingSpaceAdjunction`): the hom-set bijection
`(π₁(X, x) ⟶ G) ≃ (X ⟶ BG)` is the inverse of
`TauCeti.classifyingSpaceHomotopyFunctorHomEquiv`, which sends a pointed homotopy class to the
homomorphism it induces, read through `π₁(BG) ≅ G`. The counit is the natural isomorphism
`TauCeti.classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso` from `π₁ ∘ B` to the
identity (`TauCeti.fundamentalGroupClassifyingSpaceAdjunction_counit_app`).

The CW hypothesis on the source is needed: the Warsaw circle has trivial fundamental group but
maps to the circle, a model of `B ℤ`, by a map that is not null-homotopic.

## Main definitions

* `TauCeti.PointedHomotopyCat.isPathConnectedCWComplex`: the path-connected Hausdorff CW complexes
  in the pointed homotopy category.
* `TauCeti.classifyingSpaceCWFunctor`: the classifying-space functor into them.
* `TauCeti.fundamentalGroupCWFunctor`: the fundamental group on them.
* `TauCeti.fundamentalGroupClassifyingSpaceAdjunction`: the adjunction `π₁ ⊣ B`.
* `TauCeti.classifyingSpaceCWFunctorFullyFaithful`: as the counit is an isomorphism, `B` is fully
  faithful, with the corresponding `Full` and `Faithful` instances.

## Main results

* `TauCeti.PointedHomotopyCat.isPathConnectedCWComplex_iff`,
  `TauCeti.PointedHomotopyCat.isPathConnectedCWComplex_of`: membership in the subcategory.

* `TauCeti.fundamentalGroupClassifyingSpaceAdjunction_homEquiv_symm_apply`,
  `TauCeti.fundamentalGroupClassifyingSpaceAdjunction_homEquiv_apply`: the hom-set bijection
  sends a pointed homotopy class to the homomorphism it induces on fundamental groups.
* `TauCeti.fundamentalGroupClassifyingSpaceAdjunction_unit_app`: the unit is the class
  `X ⟶ B(π₁(X))` inducing the identity.
* `TauCeti.fundamentalGroupClassifyingSpaceAdjunction_counit_app`: the counit is
  `classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B, Proposition
  1B.9.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TauCeti

namespace PointedHomotopyCat

/-- The objects of the pointed homotopy category whose based space is a path-connected Hausdorff
CW complex, with an arbitrary base point. -/
def isPathConnectedCWComplex : ObjectProperty PointedHomotopyCat.{u} :=
  fun X ↦ T2Space X.as.carrier ∧ Nonempty (Topology.CWComplex (Set.univ : Set X.as.carrier)) ∧
    PathConnectedSpace X.as.carrier

theorem isPathConnectedCWComplex_iff {X : PointedHomotopyCat.{u}} :
    isPathConnectedCWComplex X ↔ T2Space X.as.carrier ∧
      Nonempty (Topology.CWComplex (Set.univ : Set X.as.carrier)) ∧
        PathConnectedSpace X.as.carrier :=
  Iff.rfl

/-- A path-connected Hausdorff CW complex lies in `isPathConnectedCWComplex`. -/
theorem isPathConnectedCWComplex_of {X : PointedHomotopyCat.{u}} [T2Space X.as.carrier]
    [Topology.CWComplex (Set.univ : Set X.as.carrier)] [PathConnectedSpace X.as.carrier] :
    isPathConnectedCWComplex X :=
  ⟨‹_›, ⟨‹_›⟩, ‹_›⟩

instance (X : isPathConnectedCWComplex.{u}.FullSubcategory) : T2Space X.obj.as.carrier :=
  (isPathConnectedCWComplex_iff.1 X.property).1

instance (X : isPathConnectedCWComplex.{u}.FullSubcategory) :
    PathConnectedSpace X.obj.as.carrier :=
  (isPathConnectedCWComplex_iff.1 X.property).2.2

/-- A CW structure on an object of `isPathConnectedCWComplex`, chosen from its property. It is a
local instance only: the property records that a CW structure exists, not which one. -/
@[instance_reducible] private def cwComplex (X : isPathConnectedCWComplex.{u}.FullSubcategory) :
    Topology.CWComplex (Set.univ : Set X.obj.as.carrier) :=
  (isPathConnectedCWComplex_iff.1 X.property).2.1.some

end PointedHomotopyCat

open PointedHomotopyCat

attribute [local instance] PointedHomotopyCat.cwComplex

/-- Milnor's classifying space is a path-connected Hausdorff CW complex. -/
theorem isPathConnectedCWComplex_classifyingSpaceHomotopyFunctor_obj (G : GrpCat.{u}) :
    isPathConnectedCWComplex (classifyingSpaceHomotopyFunctor.obj G) :=
  ⟨inferInstanceAs (T2Space (classifyingSpaceFunctor.obj G).carrier),
    ⟨inferInstanceAs (Topology.CWComplex (Set.univ : Set (classifyingSpaceFunctor.obj G).carrier))⟩,
    inferInstanceAs (PathConnectedSpace (classifyingSpaceFunctor.obj G).carrier)⟩

/-- The classifying-space functor, as a functor into the path-connected Hausdorff CW complexes of
the pointed homotopy category. -/
@[expose] def classifyingSpaceCWFunctor : GrpCat.{u} ⥤ isPathConnectedCWComplex.FullSubcategory :=
  ObjectProperty.lift _ classifyingSpaceHomotopyFunctor
    isPathConnectedCWComplex_classifyingSpaceHomotopyFunctor_obj

-- Not `@[simp]`: it rewrites objects inside the types of morphisms.
theorem classifyingSpaceCWFunctor_obj_obj (G : GrpCat.{u}) :
    (classifyingSpaceCWFunctor.obj G).obj = classifyingSpaceHomotopyFunctor.obj G :=
  rfl

@[simp]
theorem classifyingSpaceCWFunctor_map_hom {G G' : GrpCat.{u}} (φ : G ⟶ G') :
    (classifyingSpaceCWFunctor.map φ).hom = classifyingSpaceHomotopyFunctor.map φ :=
  rfl

/-- The fundamental group of a path-connected Hausdorff CW complex in the pointed homotopy
category. -/
@[expose] def fundamentalGroupCWFunctor :
    isPathConnectedCWComplex.{u}.FullSubcategory ⥤ GrpCat.{u} :=
  isPathConnectedCWComplex.ι ⋙ fundamentalGroupFunctor

-- Not `@[simp]`: it rewrites objects inside the types of morphisms.
theorem fundamentalGroupCWFunctor_obj (X : isPathConnectedCWComplex.{u}.FullSubcategory) :
    fundamentalGroupCWFunctor.obj X = fundamentalGroupFunctor.obj X.obj :=
  rfl

@[simp]
theorem fundamentalGroupCWFunctor_map {X Y : isPathConnectedCWComplex.{u}.FullSubcategory}
    (f : X ⟶ Y) : fundamentalGroupCWFunctor.map f = fundamentalGroupFunctor.map f.hom :=
  rfl

/-- The identification `π₁(BG) ≅ G` of
`classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`, typed for the objects of
`classifyingSpaceCWFunctor` (definitionally `classifyingSpaceHomotopyFunctor.obj G`). -/
private def counitApp (G : GrpCat.{u}) :
    fundamentalGroupFunctor.obj (classifyingSpaceCWFunctor.obj G).obj ⟶ G :=
  classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G

private theorem map_comp_counitApp {G G' : GrpCat.{u}} (φ : G ⟶ G') :
    fundamentalGroupFunctor.map (classifyingSpaceCWFunctor.map φ).hom ≫ counitApp G' =
      counitApp G ≫ φ :=
  classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.naturality φ

/-- The bijection `(π₁(X) ⟶ G) ≃ (X ⟶ BG)` underlying the adjunction: the inverse of
`classifyingSpaceHomotopyFunctorHomEquiv`, transported along the inclusion of the full
subcategory. The object `X.obj` is `PointedHomotopyCat.quotient.obj X.obj.as` by definition. -/
private def homEquiv (X : isPathConnectedCWComplex.{u}.FullSubcategory) (G : GrpCat.{u}) :
    (fundamentalGroupCWFunctor.obj X ⟶ G) ≃ (X ⟶ classifyingSpaceCWFunctor.obj G) :=
  (classifyingSpaceHomotopyFunctorHomEquiv X.obj.as G).symm.trans
    (isPathConnectedCWComplex.fullyFaithfulι.homEquiv (X := X)
      (Y := classifyingSpaceCWFunctor.obj G)).symm

private theorem homEquiv_symm_apply (X : isPathConnectedCWComplex.{u}.FullSubcategory)
    (G : GrpCat.{u}) (f : X ⟶ classifyingSpaceCWFunctor.obj G) :
    (homEquiv X G).symm f = fundamentalGroupFunctor.map f.hom ≫ counitApp G :=
  classifyingSpaceHomotopyFunctorHomEquiv_apply X.obj.as G f.hom

/-- **The fundamental group is left adjoint to the classifying space** on path-connected Hausdorff
CW complexes: pointed homotopy classes `X ⟶ BG` correspond to homomorphisms `π₁(X) ⟶ G`. -/
def fundamentalGroupClassifyingSpaceAdjunction :
    fundamentalGroupCWFunctor.{u} ⊣ classifyingSpaceCWFunctor.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := fun f g ↦ by
        rw [homEquiv_symm_apply, homEquiv_symm_apply, ObjectProperty.FullSubcategory.comp_hom,
          Functor.map_comp, Category.assoc, fundamentalGroupCWFunctor_map]
        -- As in `homEquiv_naturality_right`, the sides differ only in implicit objects, related
        -- by `fundamentalGroupCWFunctor_obj` and `classifyingSpaceCWFunctor_obj_obj`.
        rfl
      homEquiv_naturality_right := fun {X G G'} f φ ↦ (homEquiv X G').symm.injective <| by
        simp only [Equiv.symm_apply_apply, homEquiv_symm_apply,
          ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc,
          map_comp_counitApp]
        rw [← Category.assoc, ← homEquiv_symm_apply, Equiv.symm_apply_apply]
        -- The two sides differ only in the implicit source, `fundamentalGroupCWFunctor.obj X`
        -- against `fundamentalGroupFunctor.obj X.obj`, equal by `fundamentalGroupCWFunctor_obj`.
        rfl }

/-- The hom-set bijection of `fundamentalGroupClassifyingSpaceAdjunction` sends a pointed homotopy
class `X ⟶ BG` to the homomorphism it induces, read through `π₁(BG) ≅ G`. -/
@[simp]
theorem fundamentalGroupClassifyingSpaceAdjunction_homEquiv_symm_apply
    (X : isPathConnectedCWComplex.{u}.FullSubcategory) (G : GrpCat.{u})
    (f : X ⟶ classifyingSpaceCWFunctor.obj G) :
    (fundamentalGroupClassifyingSpaceAdjunction.homEquiv X G).symm f =
      fundamentalGroupFunctor.map f.hom ≫
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G := by
  rw [fundamentalGroupClassifyingSpaceAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact homEquiv_symm_apply X G f

/-- The hom-set bijection of `fundamentalGroupClassifyingSpaceAdjunction` sends a homomorphism
`φ : π₁(X) ⟶ G` to the pointed homotopy class `X ⟶ BG` inducing `φ`, read through `π₁(BG) ≅ G`.
It is stated without naming a CW structure on `X`, which `isPathConnectedCWComplex` only asserts
to exist. -/
theorem fundamentalGroupClassifyingSpaceAdjunction_homEquiv_apply
    (X : isPathConnectedCWComplex.{u}.FullSubcategory) (G : GrpCat.{u})
    (φ : fundamentalGroupCWFunctor.obj X ⟶ G) :
    fundamentalGroupFunctor.map (fundamentalGroupClassifyingSpaceAdjunction.homEquiv X G φ).hom ≫
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G = φ := by
  rw [← fundamentalGroupClassifyingSpaceAdjunction_homEquiv_symm_apply, Equiv.symm_apply_apply]

/-- The unit of `fundamentalGroupClassifyingSpaceAdjunction` at `X` is the pointed homotopy class
`X ⟶ B(π₁(X))` inducing the identity of `π₁(X)`, read through `π₁(B(π₁(X))) ≅ π₁(X)`. -/
theorem fundamentalGroupClassifyingSpaceAdjunction_unit_app
    (X : isPathConnectedCWComplex.{u}.FullSubcategory) :
    fundamentalGroupFunctor.map (fundamentalGroupClassifyingSpaceAdjunction.unit.app X).hom ≫
        classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app
          (fundamentalGroupCWFunctor.obj X) = 𝟙 _ := by
  rw [← Adjunction.homEquiv_id, fundamentalGroupClassifyingSpaceAdjunction_homEquiv_apply]
  -- Both identities are on `π₁(X)`: `(𝟭 _).obj X` is `X` and `fundamentalGroupCWFunctor.obj X` is
  -- `fundamentalGroupFunctor.obj X.obj` (`fundamentalGroupCWFunctor_obj`).
  rfl

/-- The counit of `fundamentalGroupClassifyingSpaceAdjunction` is the identification
`π₁(BG) ≅ G` of `classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso`. -/
@[simp]
theorem fundamentalGroupClassifyingSpaceAdjunction_counit_app (G : GrpCat.{u}) :
    fundamentalGroupClassifyingSpaceAdjunction.counit.app G =
      classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.hom.app G := by
  have h := fundamentalGroupClassifyingSpaceAdjunction_homEquiv_symm_apply _ G (𝟙 _)
  simp only [Adjunction.homEquiv_counit, ObjectProperty.FullSubcategory.id_hom,
    fundamentalGroupCWFunctor_map, CategoryTheory.Functor.map_id] at h
  exact h

instance (G : GrpCat.{u}) : IsIso (fundamentalGroupClassifyingSpaceAdjunction.counit.app G) := by
  rw [fundamentalGroupClassifyingSpaceAdjunction_counit_app]
  exact Iso.isIso_hom (classifyingSpaceHomotopyFunctorCompFundamentalGroupFunctorIso.app G)

instance : IsIso fundamentalGroupClassifyingSpaceAdjunction.{u}.counit :=
  NatIso.isIso_of_isIso_app _

/-- The classifying space is fully faithful as a functor into the path-connected Hausdorff CW
complexes, since the counit of `fundamentalGroupClassifyingSpaceAdjunction` is an isomorphism. -/
def classifyingSpaceCWFunctorFullyFaithful : classifyingSpaceCWFunctor.{u}.FullyFaithful :=
  fundamentalGroupClassifyingSpaceAdjunction.fullyFaithfulROfIsIsoCounit

instance : classifyingSpaceCWFunctor.{u}.Full := classifyingSpaceCWFunctorFullyFaithful.full

instance : classifyingSpaceCWFunctor.{u}.Faithful := classifyingSpaceCWFunctorFullyFaithful.faithful

end TauCeti
