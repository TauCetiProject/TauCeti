/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.AlgebraicTopology.Quasicategory.StrictBicategory
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import TauCeti.AlgebraicTopology.Quasicategory.HomotopyCategory
public import TauCeti.AlgebraicTopology.SimplicialSet.HoFunctorIhom
public import TauCeti.AlgebraicTopology.SimplicialSet.Nerve.FunctorCategory
public import TauCeti.CategoryTheory.Bicategory.Adjunction.Basic

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
* `SSet.QCat.nonempty_iso_homMk_pre_app`: an invertible `2`-morphism `h ≅ h'` gives an invertible
  `2`-morphism between the precomposition maps `Fun(Y, E) ⟶ Fun(X, E)`.
* `SSet.QCat.IsCategoricalEquivalence`: categorical equivalences of quasicategories, with
  `SSet.QCat.isCategoricalEquivalence_iff_exists_equivalence` identifying them with the
  `1`-morphisms underlying equivalences in the bicategory. They contain the isomorphisms, are
  closed under composition, are invariant under invertible `2`-morphisms and satisfy two out of
  three.
* `SSet.QCat.IsCategoricalEquivalence.pre_app`: precomposition `Fun(Y, E) ⟶ Fun(X, E)` with a
  categorical equivalence `X ⟶ Y` is a categorical equivalence.
* `SSet.QCat.IsCategoricalEquivalence.isEquivalence_mapHomotopyCategory`: a categorical
  equivalence induces an equivalence of homotopy categories.
* `SSet.QCat.IsCategoricalEquivalence.exists_isEquivalence`: a categorical equivalence is
  essentially surjective, every vertex of the target being joined by an equivalence to a vertex of
  the image.
* `SSet.QCat.IsCategoricalEquivalence.isEquivalence_map_iff`: a categorical equivalence preserves
  and reflects equivalences.
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

open CategoryTheory MonoidalCategory MonoidalClosed Simplicial

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

/-- The invertible `2`-morphisms `f ≅ g` of the bicategory of quasicategories are the
isomorphisms between the corresponding objects of the hom-category. -/
private lemma nonempty_iso_iff_nonempty_iso_homEquiv {f g : X ⟶ Y} :
    Nonempty (f ≅ g) ↔ Nonempty (CatEnrichedOrdinary.homEquiv f ≅ CatEnrichedOrdinary.homEquiv g) :=
  ⟨fun ⟨α⟩ ↦ ⟨{ hom := α.hom.base
                inv := α.inv.base
                hom_inv_id := congrArg CatEnrichedOrdinary.Hom.base α.hom_inv_id
                inv_hom_id := congrArg CatEnrichedOrdinary.Hom.base α.inv_hom_id }⟩,
    fun ⟨β⟩ ↦ ⟨{ hom := .mk β.hom
                 inv := .mk β.inv
                 hom_inv_id := CatEnrichedOrdinary.Hom.ext _ _ β.hom_inv_id
                 inv_hom_id := CatEnrichedOrdinary.Hom.ext _ _ β.inv_hom_id }⟩⟩

/-- An invertible `2`-morphism `h ≅ h'` between maps `X ⟶ Y` of quasicategories gives an
invertible `2`-morphism between the precomposition maps `Fun(Y, E) ⟶ Fun(X, E)`. -/
lemma nonempty_iso_homMk_pre_app {h h' : X ⟶ Y} (α : h ≅ h') (E : SSet.{u}) [Quasicategory E] :
    Nonempty ((ObjectProperty.homMk ((pre h.hom).app E) :
        (⟨(ihom Y.obj).obj E, inferInstance⟩ : QCat.{u}) ⟶ ⟨(ihom X.obj).obj E, inferInstance⟩) ≅
      ObjectProperty.homMk ((pre h'.hom).app E)) := by
  -- The object of the hom-category `Z ⟶ W` given by `k` is the vertex of `Fun(Z, W)` given by
  -- the global element `curry' k.hom`: by definition it is given by `eHomEquiv SSet k`, which
  -- uncurries to `k.hom`.
  have hv {Z W : QCat.{u}} (k : Z ⟶ W) : CatEnrichedOrdinary.homEquiv k =
      HomotopyCategory.mk (unitHomEquiv _ (curry' k.hom)) :=
    congrArg (fun φ ↦ HomotopyCategory.mk (unitHomEquiv ((ihom Z.obj).obj W.obj) φ))
      (curry'_uncurry' (eHomEquiv SSet k : 𝟙_ SSet ⟶ (ihom Z.obj).obj W.obj)).symm
  -- Precomposition as a map of function complexes `Fun(X, Y) ⟶ Fun(Fun(Y, E), Fun(X, E))`.
  let c : (ihom X.obj).obj Y.obj ⟶ (ihom ((ihom Y.obj).obj E)).obj ((ihom X.obj).obj E) :=
    curry ((β_ _ _).hom ≫ comp X.obj Y.obj E)
  have hc (k : X.obj ⟶ Y.obj) : c.app _ (unitHomEquiv _ (curry' k)) =
      unitHomEquiv _ (curry' ((pre k).app E)) := by
    -- The image under `c` of the vertex given by the global element `curry' k` is the vertex
    -- given by the global element `curry' k ≫ c`, by definition of `unitHomEquiv`.
    change unitHomEquiv _ (curry' k ≫ c) = _
    rw [← curry'_uncurry' (curry' k ≫ c), uncurry', uncurry_natural_left, uncurry_curry,
      BraidedCategory.braiding_naturality_right_assoc, curry'_whiskerRight_comp]
    simp
  obtain ⟨β⟩ := nonempty_iso_iff_nonempty_iso_homEquiv.1 ⟨α⟩
  refine (nonempty_iso_iff_nonempty_iso_homEquiv (X := ⟨(ihom Y.obj).obj E, inferInstance⟩)
    (Y := ⟨(ihom X.obj).obj E, inferInstance⟩)).2 ⟨eqToIso ?_ ≪≫
      (mapHomotopyCategory c).mapIso β ≪≫ eqToIso ?_⟩
  · rw [hv, hv]
    exact congrArg HomotopyCategory.mk (hc _).symm
  · rw [hv, hv]
    exact congrArg HomotopyCategory.mk (hc _)

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

/-- An isomorphism of quasicategories is a categorical equivalence. -/
lemma of_isIso (f : X ⟶ Y) [IsIso f] : IsCategoricalEquivalence f :=
  ⟨inv f, ⟨eqToIso (IsIso.hom_inv_id f).symm⟩, ⟨eqToIso (IsIso.inv_hom_id f)⟩⟩

/-- Categorical equivalences are invariant under invertible `2`-morphisms. -/
lemma of_iso {f f' : X ⟶ Y} (i : f ≅ f') (hf : IsCategoricalEquivalence f) :
    IsCategoricalEquivalence f' := by
  obtain ⟨e, rfl⟩ := (isCategoricalEquivalence_iff_exists_equivalence _).1 hf
  exact (isCategoricalEquivalence_iff_exists_equivalence _).2
    ⟨.mkOfAdjointifyCounit (e.unit ≪≫ Bicategory.whiskerRightIso i e.inv)
      (Bicategory.whiskerLeftIso e.inv i.symm ≪≫ e.counit), rfl⟩

/-- **Two out of three** for categorical equivalences: if `f` and `f ≫ g` are categorical
equivalences, so is `g`. -/
lemma of_comp_left {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsCategoricalEquivalence f)
    (hfg : IsCategoricalEquivalence (f ≫ g)) : IsCategoricalEquivalence g := by
  obtain ⟨e, rfl⟩ := (isCategoricalEquivalence_iff_exists_equivalence f).1 hf
  exact of_iso ((Bicategory.associator _ _ _).symm ≪≫ Bicategory.whiskerRightIso e.counit g ≪≫
    Bicategory.leftUnitor g)
    (((isCategoricalEquivalence_iff_exists_equivalence _).2 ⟨e.symm, rfl⟩).comp hfg)

/-- **Two out of three** for categorical equivalences: if `g` and `f ≫ g` are categorical
equivalences, so is `f`. -/
lemma of_comp_right {f : X ⟶ Y} {g : Y ⟶ Z} (hg : IsCategoricalEquivalence g)
    (hfg : IsCategoricalEquivalence (f ≫ g)) : IsCategoricalEquivalence f := by
  obtain ⟨e, rfl⟩ := (isCategoricalEquivalence_iff_exists_equivalence _).1 hg
  exact of_iso (Bicategory.associator _ _ _ ≪≫ Bicategory.whiskerLeftIso f e.unit.symm ≪≫
    Bicategory.rightUnitor f)
    (hfg.comp ((isCategoricalEquivalence_iff_exists_equivalence _).2 ⟨e.symm, rfl⟩))

/-- Precomposition `Fun(Y, E) ⟶ Fun(X, E)` with a categorical equivalence `g : X ⟶ Y` is a
categorical equivalence, with quasi-inverse the precomposition with a quasi-inverse of `g`. -/
lemma pre_app {g : X ⟶ Y} (hg : IsCategoricalEquivalence g) (E : SSet.{u}) [Quasicategory E] :
    IsCategoricalEquivalence (X := ⟨(ihom Y.obj).obj E, inferInstance⟩)
      (Y := ⟨(ihom X.obj).obj E, inferInstance⟩) (ObjectProperty.homMk ((pre g.hom).app E)) := by
  obtain ⟨e, rfl⟩ := (isCategoricalEquivalence_iff_exists_equivalence _).1 hg
  obtain ⟨α⟩ := nonempty_iso_homMk_pre_app e.counit E
  obtain ⟨β⟩ := nonempty_iso_homMk_pre_app e.unit E
  refine (isCategoricalEquivalence_iff_exists_equivalence _).2
    ⟨.mkOfAdjointifyCounit (g := ObjectProperty.homMk ((pre e.inv.hom).app E))
      (eqToIso ?_ ≪≫ α.symm ≪≫ eqToIso ?_) (eqToIso ?_ ≪≫ β.symm ≪≫ eqToIso ?_), rfl⟩
  all_goals ext1
  -- The `1`-morphisms of the bicategory of quasicategories compose as maps of simplicial sets.
  · exact (NatTrans.congr_app (pre_id Y.obj) E).symm
  · exact NatTrans.congr_app (pre_map e.inv.hom e.hom.hom) E
  · exact (NatTrans.congr_app (pre_map e.hom.hom e.inv.hom) E).symm
  · exact NatTrans.congr_app (pre_id X.obj) E

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

/-- A categorical equivalence of quasicategories is essentially surjective: every vertex of the
target is joined by an equivalence to a vertex in its image. -/
lemma exists_isEquivalence {f : X ⟶ Y} (hf : IsCategoricalEquivalence f) (y : Y.obj _⦋0⦌) :
    ∃ (x : X.obj _⦋0⦌) (e : Edge (f.hom.app _ x) y), e.IsEquivalence :=
  have := Y.property
  have := hf.isEquivalence_mapHomotopyCategory
  (essSurj_mapHomotopyCategory_iff f.hom).1 inferInstance y

/-- A categorical equivalence of quasicategories preserves and reflects equivalences. -/
lemma isEquivalence_map_iff {f : X ⟶ Y} (hf : IsCategoricalEquivalence f) {x₀ x₁ : X.obj _⦋0⦌}
    (e : Edge x₀ x₁) : (e.map f.hom).IsEquivalence ↔ e.IsEquivalence := by
  have := X.property
  have := Y.property
  have := hf.isEquivalence_mapHomotopyCategory
  rw [Edge.isEquivalence_iff_isIso_homotopyCategoryHomMk,
    Edge.isEquivalence_iff_isIso_homotopyCategoryHomMk, ← mapHomotopyCategory_map_homMk]
  exact isIso_iff_of_reflects_iso _ _

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
