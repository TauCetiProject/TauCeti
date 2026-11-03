/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import TauCeti.AlgebraicTopology.SimplicialSet.HoFunctorIhom
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.FunctorCategory
public import TauCeti.CategoryTheory.Bicategory.Equivalence

/-!
# Categorical equivalences of quasicategories

Mathlib's strict bicategory `SSet.QCat.bicategory` has quasicategories as objects, maps of
simplicial sets as `1`-morphisms, and as hom-categories the homotopy categories of the
simplicial internal homs `Fun(X, Y)`. A map `f : X ⟶ Y` of quasicategories is a *categorical
equivalence* when it is an equivalence in this bicategory: it has a quasi-inverse `g` together
with invertible natural transformations `𝟙 ≅ f ≫ g` and `g ≫ f ≅ 𝟙` in the homotopy categories
of `Fun(X, X)` and `Fun(Y, Y)`.

Equivalence of homotopy categories alone is weaker, since categorical equivalences also identify
the higher mapping spaces. The comparison in the other direction is supplied here: the homotopy
category functor acts on hom-categories through `SSet.ihomHoFunctor`, so every categorical
equivalence induces an equivalence of homotopy categories. For nerves of ordinary categories the
two notions agree with equivalence of categories.

## Main declarations

* `SSet.QCat.homotopyCategoryFunctor X Y`: the functor from the hom-category `X ⟶ Y` of the
  bicategory of quasicategories to `ho X ⥤ ho Y`, which sends `f` to `mapHomotopyCategory f.hom`.
* `SSet.QCat.IsCategoricalEquivalence`: categorical equivalences of quasicategories, with
  `SSet.QCat.isCategoricalEquivalence_iff_exists_equivalence` identifying them with the
  `1`-morphisms underlying equivalences in the bicategory. They contain the identities and are
  closed under composition.
* `SSet.QCat.IsCategoricalEquivalence.isEquivalence_mapHomotopyCategory`: a categorical
  equivalence induces an equivalence of homotopy categories.
* `CategoryTheory.Iso.nerveMap`: a natural isomorphism of functors gives an invertible natural
  transformation between their nerves, with components computed by
  `CategoryTheory.Iso.nerveMap_hom_base` and `CategoryTheory.Iso.nerveMap_inv_base`.
* `SSet.QCat.isCategoricalEquivalence_homMk_nerveMap_iff`: a functor between categories is an
  equivalence exactly when its nerve is a categorical equivalence.

## References

* J. Lurie, *Higher Topos Theory*, §1.2.10.
* E. Riehl and D. Verity, *The 2-category theory of quasi-categories*, Adv. Math. 280 (2015).
-/

public section

universe u

open CategoryTheory MonoidalCategory Simplicial

namespace SSet.QCat

/-- The hom-categories of the bicategory of quasicategories, made available to instance
search on the type `X ⟶ Y` of maps of quasicategories. -/
instance homCategory (X Y : QCat.{u}) : Category (X ⟶ Y) := Bicategory.homCategory X Y

variable {X Y Z : QCat.{u}}

/-- The functor from the hom-category `X ⟶ Y` of the bicategory of quasicategories to the
category of functors between the homotopy categories. It sends a map `f` to
`mapHomotopyCategory f.hom`, see `homotopyCategoryFunctor_obj`. -/
noncomputable def homotopyCategoryFunctor (X Y : QCat.{u}) :
    (X ⟶ Y) ⥤ (X.obj.HomotopyCategory ⥤ Y.obj.HomotopyCategory) where
  obj f := (ihomHoFunctor X.obj Y.obj).obj (CatEnrichedOrdinary.homEquiv f)
  map α := (ihomHoFunctor X.obj Y.obj).map α.base
  map_id _ := (ihomHoFunctor X.obj Y.obj).map_id _
  map_comp α β := (ihomHoFunctor X.obj Y.obj).map_comp α.base β.base

@[simp]
lemma homotopyCategoryFunctor_obj (f : X ⟶ Y) :
    (homotopyCategoryFunctor X Y).obj f = mapHomotopyCategory f.hom :=
  -- The vertex of `Fun(X, Y)` classified by `f` is `natTransEquiv.symm f.hom`, which
  -- uncurries to `f.hom` by definition.
  ihomHoFunctor_obj_mk _

/-- The value of `homotopyCategoryFunctor X Y` on `f` is the value of `ihomHoFunctor` on the
vertex of `Fun(X, Y)` corresponding to `f`. -/
lemma homotopyCategoryFunctor_obj_eq_ihomHoFunctor_obj (f : X ⟶ Y) :
    (homotopyCategoryFunctor X Y).obj f =
      (ihomHoFunctor X.obj Y.obj).obj (CatEnrichedOrdinary.homEquiv f) :=
  (rfl)

/-- On a `2`-morphism `α`, the functor `homotopyCategoryFunctor X Y` is `ihomHoFunctor` applied to
the underlying morphism of `ho Fun(X, Y)`; its components are computed on edges by
`ihomHoFunctor_map_homMk_app`. -/
@[simp]
lemma homotopyCategoryFunctor_map {f g : X ⟶ Y} (α : f ⟶ g) :
    (homotopyCategoryFunctor X Y).map α =
      eqToHom (homotopyCategoryFunctor_obj_eq_ihomHoFunctor_obj f) ≫
        (ihomHoFunctor X.obj Y.obj).map α.base ≫
        eqToHom (homotopyCategoryFunctor_obj_eq_ihomHoFunctor_obj g).symm :=
  ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- A map of quasicategories is a categorical equivalence when it is an equivalence in the
bicategory of quasicategories: it admits a quasi-inverse together with invertible natural
transformations relating the two composites with the identities. -/
def IsCategoricalEquivalence (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, Nonempty (𝟙 X ≅ f ≫ g) ∧ Nonempty (g ≫ f ≅ 𝟙 Y)

/-- Categorical equivalences are the `1`-morphisms underlying equivalences in the bicategory of
quasicategories. -/
lemma isCategoricalEquivalence_iff_exists_equivalence (f : X ⟶ Y) :
    IsCategoricalEquivalence f ↔ ∃ e : Bicategory.Equivalence X Y, e.hom = f :=
  ⟨fun ⟨_, ⟨η⟩, ⟨ε⟩⟩ ↦ ⟨.mkOfAdjointifyCounit η ε, rfl⟩,
    fun ⟨e, he⟩ ↦ he ▸ ⟨e.inv, ⟨e.unit⟩, ⟨e.counit⟩⟩⟩

namespace IsCategoricalEquivalence

/-- The identity of a quasicategory is a categorical equivalence. -/
lemma id (X : QCat.{u}) : IsCategoricalEquivalence (𝟙 X) :=
  (isCategoricalEquivalence_iff_exists_equivalence _).2 ⟨.id X, rfl⟩

/-- Categorical equivalences are closed under composition. -/
lemma comp {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsCategoricalEquivalence f)
    (hg : IsCategoricalEquivalence g) : IsCategoricalEquivalence (f ≫ g) := by
  obtain ⟨e, rfl⟩ := (isCategoricalEquivalence_iff_exists_equivalence f).1 hf
  obtain ⟨e', rfl⟩ := (isCategoricalEquivalence_iff_exists_equivalence g).1 hg
  exact (isCategoricalEquivalence_iff_exists_equivalence _).2
    ⟨e.trans e', Bicategory.Equivalence.trans_hom e e'⟩

/-- A categorical equivalence of quasicategories induces an equivalence of homotopy
categories. -/
lemma isEquivalence_mapHomotopyCategory {f : X ⟶ Y} (hf : IsCategoricalEquivalence f) :
    (mapHomotopyCategory f.hom).IsEquivalence := by
  obtain ⟨g, ⟨η⟩, ⟨ε⟩⟩ := hf
  have hid (Z : QCat.{u}) : mapHomotopyCategory (𝟙 Z.obj) = 𝟭 _ :=
    congrArg Cat.Hom.toFunctor (hoFunctor.map_id Z.obj)
  have hcomp {Z W V : QCat.{u}} (h : Z ⟶ W) (h' : W ⟶ V) :
      mapHomotopyCategory (h.hom ≫ h'.hom) =
        mapHomotopyCategory h.hom ⋙ mapHomotopyCategory h'.hom :=
    congrArg Cat.Hom.toFunctor (hoFunctor.map_comp h.hom h'.hom)
  let e {Z W : QCat.{u}} {h h' : Z ⟶ W} (α : h ≅ h') :
      mapHomotopyCategory h.hom ≅ mapHomotopyCategory h'.hom :=
    eqToIso (homotopyCategoryFunctor_obj h).symm ≪≫ (homotopyCategoryFunctor Z W).mapIso α ≪≫
      eqToIso (homotopyCategoryFunctor_obj h')
  exact (CategoryTheory.Equivalence.mk (mapHomotopyCategory f.hom) (mapHomotopyCategory g.hom)
    (eqToIso (hid X).symm ≪≫ e η ≪≫ eqToIso (hcomp f g))
    (eqToIso (hcomp g f).symm ≪≫ e ε ≪≫ eqToIso (hid Y))).isEquivalence_functor

end IsCategoricalEquivalence

end SSet.QCat

/-! ### Nerves of categories -/

section nerve

variable {C D : Type u} [Category.{u} C] [Category.{u} D]

namespace CategoryTheory.Iso

open SSet

/-- A natural isomorphism `F ≅ G` gives an invertible `2`-morphism between the nerves of `F`
and `G` in the bicategory of quasicategories. -/
noncomputable def nerveMap {F G : C ⥤ D} (α : F ≅ G) :
    (ObjectProperty.homMk (nerveMap F) :
      (⟨nerve C, inferInstance⟩ : QCat.{u}) ⟶ ⟨nerve D, inferInstance⟩) ≅
      ObjectProperty.homMk (nerveMap G) :=
  let β : HomotopyCategory.mk
      (unitHomEquiv _ (Functor.natTransEquiv.symm (CategoryTheory.nerveMap F))) ≅
      .mk (unitHomEquiv _ (Functor.natTransEquiv.symm (CategoryTheory.nerveMap G))) :=
    eqToIso (congrArg HomotopyCategory.mk
        (TauCeti.nerveFunctorCategoryToIhom_app_nerveEquiv_symm F)).symm ≪≫
      (mapHomotopyCategory (TauCeti.nerveFunctorCategoryToIhom C D)).mapIso
        α.toNerveHomotopyCategory ≪≫
      eqToIso (congrArg HomotopyCategory.mk
        (TauCeti.nerveFunctorCategoryToIhom_app_nerveEquiv_symm G))
  { hom := .mk β.hom
    inv := .mk β.inv
    hom_inv_id := CatEnrichedOrdinary.Hom.ext _ _ β.hom_inv_id
    inv_hom_id := CatEnrichedOrdinary.Hom.ext _ _ β.inv_hom_id }

/-- The `2`-cell `α.nerveMap.hom` is the image under the comparison `N(C ⥤ D) ⟶ Fun(N C, N D)`
of the edge of `N(C ⥤ D)` given by `α.hom`. -/
@[simp]
lemma nerveMap_hom_base {F G : C ⥤ D} (α : F ≅ G) :
    α.nerveMap.hom.base =
      eqToHom (congrArg HomotopyCategory.mk
          (TauCeti.nerveFunctorCategoryToIhom_app_nerveEquiv_symm F)).symm ≫
        HomotopyCategory.homMk ((nerve.edgeMk α.hom).map (TauCeti.nerveFunctorCategoryToIhom C D)) ≫
        eqToHom (congrArg HomotopyCategory.mk
          (TauCeti.nerveFunctorCategoryToIhom_app_nerveEquiv_symm G)) := by
  -- `Hom.base (Hom.mk β.hom) = β.hom` holds by `CatEnrichedOrdinary.base_mk`, but `rw`/`simp`
  -- cannot rewrite the resulting `Iso.trans` and `Functor.mapIso` projections: the objects of
  -- `QCat` only become objects of `CatEnrichedOrdinary QCat` (as `homEquiv` expects) after
  -- unfolding, so the goal is not type-correct at implicit transparency. The `change` unfolds
  -- `nerveMap`, `Hom.base ∘ Hom.mk`, `Iso.trans_hom`, `eqToIso.hom` and `Functor.mapIso_hom`
  -- definitionally, leaving the middle factor `(mapHomotopyCategory _).map _`.
  change _ ≫ (mapHomotopyCategory _).map α.toNerveHomotopyCategory.hom ≫ _ = _
  rw [toNerveHomotopyCategory_hom]
  -- The remaining step is `mapHomotopyCategory_map_homMk`, which holds by `rfl`.
  rfl

/-- The `2`-cell `α.nerveMap.inv` is the image under the comparison `N(C ⥤ D) ⟶ Fun(N C, N D)`
of the edge of `N(C ⥤ D)` given by `α.inv`. -/
@[simp]
lemma nerveMap_inv_base {F G : C ⥤ D} (α : F ≅ G) :
    α.nerveMap.inv.base =
      eqToHom (congrArg HomotopyCategory.mk
          (TauCeti.nerveFunctorCategoryToIhom_app_nerveEquiv_symm G)).symm ≫
        HomotopyCategory.homMk ((nerve.edgeMk α.inv).map (TauCeti.nerveFunctorCategoryToIhom C D)) ≫
        eqToHom (congrArg HomotopyCategory.mk
          (TauCeti.nerveFunctorCategoryToIhom_app_nerveEquiv_symm F)) := by
  -- As in `nerveMap_hom_base`, `change` unfolds `nerveMap`, `Hom.base ∘ Hom.mk`,
  -- `Iso.trans_inv`, `eqToIso.inv` and `Functor.mapIso_inv` definitionally, since the goal is not
  -- type-correct at implicit transparency for `rw`/`simp`. `Iso.trans_inv` reverses the order,
  -- so the composite is left-associated.
  change (_ ≫ (mapHomotopyCategory _).map α.toNerveHomotopyCategory.inv) ≫ _ = _
  rw [toNerveHomotopyCategory_inv]
  -- After `mapHomotopyCategory_map_homMk` (definitional), only reassociation remains.
  exact Category.assoc _ _ _

end CategoryTheory.Iso

namespace SSet.QCat

/-- A functor between categories is an equivalence exactly when its nerve is a categorical
equivalence of quasicategories. -/
lemma isCategoricalEquivalence_homMk_nerveMap_iff (F : C ⥤ D) :
    IsCategoricalEquivalence (X := ⟨nerve C, inferInstance⟩) (Y := ⟨nerve D, inferInstance⟩)
      (ObjectProperty.homMk (nerveMap F)) ↔ F.IsEquivalence := by
  refine ⟨fun h ↦ ?_, fun _ ↦ ⟨ObjectProperty.homMk (nerveMap F.inv),
    ⟨F.asEquivalence.unitIso.nerveMap⟩, ⟨F.asEquivalence.counitIso.nerveMap⟩⟩⟩
  -- The counit `ho (N E) ≅ E` of the nerve adjunction is natural in `E`.
  let c (E : Type u) [Category.{u} E] :=
    Cat.equivOfIso (nerveFunctorCompHoFunctorIso.app (Cat.of E))
  have hc : mapHomotopyCategory (nerveMap F) ⋙ (c D).functor = (c C).functor ⋙ F :=
    congrArg Cat.Hom.toFunctor (nerveFunctorCompHoFunctorIso.hom.naturality F.toCatHom)
  let e := (c C).symm.trans
    ((@Functor.asEquivalence _ _ _ _ _ h.isEquivalence_mapHomotopyCategory).trans (c D))
  exact (e.changeFunctor (Functor.isoWhiskerLeft (c C).inverse (eqToIso hc) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (c C).counitIso F ≪≫
      F.leftUnitor)).isEquivalence_functor

end SSet.QCat

end nerve
