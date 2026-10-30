/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Restricting a family of categories to stable full subcategories

Let `F : B ⥤ᵖ Cat` be a pseudofunctor out of a locally discrete bicategory, that is, a family of
categories `F.obj b` with transport functors `F.map f`, coherent up to the comparison
isomorphisms `F.mapId` and `F.mapComp`. Suppose that for each `b` we are given an object property
`P b` of `F.obj b`, and that every transport functor `F.map f : F.obj b ⟶ F.obj b'` sends objects
satisfying `P b` to objects satisfying `P b'`. Then the full subcategories `(P b).FullSubcategory`
form a family of categories again:

* `CategoryTheory.Pseudofunctor.fullSubcategory F P hP` is the pseudofunctor with values the full
  subcategories, whose transport functors are the lifts of those of `F`. Its unit and composition
  comparisons have as underlying morphisms the components of `F.mapId` and `F.mapComp`.
* `CategoryTheory.Pseudofunctor.fullSubcategoryι F P hP` is the inclusion, a strong transformation
  to `F` whose components are the inclusions `(P b).ι` and whose naturality isomorphisms are
  identities.

This is the analogue for families of categories of the restriction of a categorical action to a
stable full subcategory (`CategoryTheory.ObjectProperty.fullSubcategoryMonoidalLeftAction`). The
inclusion records that the transport functors of the restricted family are the transport functors
of `F`, together with their unit and composition comparisons, and not merely objectwise
isomorphic to them.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, arXiv:2002.06055, Chapter 4, for
  pseudofunctors and strong transformations.
-/

@[expose] public section

universe w₁ w₂ w v u

namespace CategoryTheory.Pseudofunctor

open Bicategory

variable {B : Type w} [Bicategory.{w₁, w₂} B] [IsLocallyDiscrete B] (F : B ⥤ᵖ Cat.{v, u})
  (P : ∀ b : B, ObjectProperty (F.obj b))
  (hP : ∀ {b b' : B} (f : b ⟶ b') (X : F.obj b), P b X → P b' ((F.map f).toFunctor.obj X))

/-- The restriction of a pseudofunctor `F : B ⥤ᵖ Cat` to full subcategories `(P b).FullSubcategory`
that are preserved by the transport functors. The transport functor along `f : b ⟶ b'` is the lift
of `F.map f`, and the unit and composition comparisons are the lifts of those of `F`. -/
def fullSubcategory : B ⥤ᵖ Cat.{v, u} :=
  pseudofunctorOfIsLocallyDiscrete (fun b ↦ Cat.of (P b).FullSubcategory)
    (fun {b b'} f ↦ ((P b').lift ((P b).ι ⋙ (F.map f).toFunctor)
      (fun X ↦ hP f _ X.property)).toCatHom)
    (fun b ↦ Cat.Hom.isoMk (NatIso.ofComponents
      (fun X ↦ (P b).isoMk ((Cat.Hom.toNatIso (F.mapId b)).app X.obj))
      (fun f ↦ by ext; exact (Cat.Hom.toNatIso (F.mapId b)).hom.naturality f.hom)))
    (fun f g ↦ Cat.Hom.isoMk (NatIso.ofComponents
      (fun X ↦ (P _).isoMk ((Cat.Hom.toNatIso (F.mapComp f g)).app X.obj))
      (fun φ ↦ by ext; exact (Cat.Hom.toNatIso (F.mapComp f g)).hom.naturality φ.hom)))
    -- Each coherence condition is checked on underlying morphisms, where it is the corresponding
    -- coherence condition of `F`; the `2`-morphisms of `B` are identities, sent to `eqToHom`.
    (fun f g h ↦ by
      ext X
      apply ObjectProperty.hom_ext
      have := congrArg (fun η ↦ η.toNatTrans.app X.obj) (F.map₂_associator f g h)
      simp only [PrelaxFunctor.map₂_eq_eqToHom, Cat.eqToHom_app] at this
      rw [Cat.eqToHom_app, ObjectProperty.eqToHom_hom]
      simpa using this.symm)
    (fun f ↦ by
      ext X
      apply ObjectProperty.hom_ext
      have := congrArg (fun η ↦ η.toNatTrans.app X.obj) (F.map₂_left_unitor f)
      simp only [PrelaxFunctor.map₂_eq_eqToHom, Cat.eqToHom_app] at this
      rw [Cat.eqToHom_app, ObjectProperty.eqToHom_hom]
      simpa using this.symm)
    (fun f ↦ by
      ext X
      apply ObjectProperty.hom_ext
      have := congrArg (fun η ↦ η.toNatTrans.app X.obj) (F.map₂_right_unitor f)
      simp only [PrelaxFunctor.map₂_eq_eqToHom, Cat.eqToHom_app] at this
      rw [Cat.eqToHom_app, ObjectProperty.eqToHom_hom]
      simpa using this.symm)

variable {F P hP}

@[simp]
lemma fullSubcategory_obj (b : B) :
    (F.fullSubcategory P hP).obj b = Cat.of (P b).FullSubcategory :=
  rfl

/-- The transport functors of the restricted family are those of `F` on underlying objects. -/
@[simp]
lemma fullSubcategory_map_toFunctor_obj_obj {b b' : B} (f : b ⟶ b')
    (X : (P b).FullSubcategory) :
    (((F.fullSubcategory P hP).map f).toFunctor.obj X).obj = (F.map f).toFunctor.obj X.obj :=
  rfl

/-- The transport functors of the restricted family are those of `F` on underlying morphisms. -/
@[simp]
lemma fullSubcategory_map_toFunctor_map_hom {b b' : B} (f : b ⟶ b')
    {X Y : (P b).FullSubcategory} (φ : X ⟶ Y) :
    (((F.fullSubcategory P hP).map f).toFunctor.map φ).hom = (F.map f).toFunctor.map φ.hom :=
  rfl

/-- Forgetting after transport in the restricted family is transport in `F` after forgetting. -/
lemma fullSubcategory_map_toFunctor_comp_ι {b b' : B} (f : b ⟶ b') :
    ((F.fullSubcategory P hP).map f).toFunctor ⋙ (P b').ι = (P b).ι ⋙ (F.map f).toFunctor :=
  rfl

@[simp]
lemma fullSubcategory_mapId_hom_toNatTrans_app_hom (b : B) (X : (P b).FullSubcategory) :
    (((F.fullSubcategory P hP).mapId b).hom.toNatTrans.app X).hom =
      (F.mapId b).hom.toNatTrans.app X.obj :=
  rfl

@[simp]
lemma fullSubcategory_mapId_inv_toNatTrans_app_hom (b : B) (X : (P b).FullSubcategory) :
    (((F.fullSubcategory P hP).mapId b).inv.toNatTrans.app X).hom =
      (F.mapId b).inv.toNatTrans.app X.obj :=
  rfl

@[simp]
lemma fullSubcategory_mapComp_hom_toNatTrans_app_hom {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁)
    (g : b₁ ⟶ b₂) (X : (P b₀).FullSubcategory) :
    (((F.fullSubcategory P hP).mapComp f g).hom.toNatTrans.app X).hom =
      (F.mapComp f g).hom.toNatTrans.app X.obj :=
  rfl

@[simp]
lemma fullSubcategory_mapComp_inv_toNatTrans_app_hom {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁)
    (g : b₁ ⟶ b₂) (X : (P b₀).FullSubcategory) :
    (((F.fullSubcategory P hP).mapComp f g).inv.toNatTrans.app X).hom =
      (F.mapComp f g).inv.toNatTrans.app X.obj :=
  rfl

variable (F P hP)

/-- The inclusion of the restricted family into `F`, as a strong transformation. Its component
at `b` is the inclusion `(P b).ι` and its naturality isomorphisms are identities. -/
def fullSubcategoryι : StrongTrans (F.fullSubcategory P hP) F where
  app b := Cat.Hom.ofFunctor (P b).ι
  naturality f := Iso.refl _
  -- The component `(P b).ι` has source `(P b).FullSubcategory`, of which
  -- `(F.fullSubcategory P hP).obj b` is only definitionally the bundling, so the component lemmas
  -- of `Cat` do not apply to the composites below. The conditions are instead stated
  -- componentwise and closed by definitional unfolding of the components, as for
  -- `CategoryTheory.MonoidalCategory.MonoidalLeftAction.strongTrans`.
  naturality_naturality η := by
    obtain rfl := obj_ext_of_isDiscrete η
    rw [Subsingleton.elim η (𝟙 _)]
    simp only [PrelaxFunctor.map₂_id]
    ext X
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  naturality_id b := by
    have h (X : (P b).FullSubcategory) : 𝟙 _ ≫ (F.mapId b).hom.toNatTrans.app X.obj =
        (F.mapId b).hom.toNatTrans.app X.obj ≫ 𝟙 _ ≫ 𝟙 _ := by
      simp
    ext X
    exact h X
  naturality_comp f g := by
    have h (X : (P _).FullSubcategory) : 𝟙 _ ≫ (F.mapComp f g).hom.toNatTrans.app X.obj =
        (F.mapComp f g).hom.toNatTrans.app X.obj ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫
          (F.map g).toFunctor.map (𝟙 _) ≫ 𝟙 _ := by
      simp
    ext X
    exact h X

variable {F P hP}

@[simp]
lemma fullSubcategoryι_app_toFunctor (b : B) :
    ((F.fullSubcategoryι P hP).app b).toFunctor = (P b).ι :=
  rfl

@[simp]
lemma fullSubcategoryι_naturality_hom_toNatTrans_app {b b' : B} (f : b ⟶ b')
    (X : (P b).FullSubcategory) :
    ((F.fullSubcategoryι P hP).naturality f).hom.toNatTrans.app X =
      𝟙 ((F.map f).toFunctor.obj X.obj) :=
  rfl

@[simp]
lemma fullSubcategoryι_naturality_inv_toNatTrans_app {b b' : B} (f : b ⟶ b')
    (X : (P b).FullSubcategory) :
    ((F.fullSubcategoryι P hP).naturality f).inv.toNatTrans.app X =
      𝟙 ((F.map f).toFunctor.obj X.obj) :=
  rfl

end CategoryTheory.Pseudofunctor
