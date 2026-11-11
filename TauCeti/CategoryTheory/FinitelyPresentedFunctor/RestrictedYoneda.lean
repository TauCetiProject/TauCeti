/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.Basic
public import TauCeti.CategoryTheory.Preadditive.RestrictedYoneda

/-!
# Finitely presented functors on a subcategory of projective objects

Let `C` be an abelian category and let `P` be a property of objects of `C` satisfied only by
projective objects. Restricting representable functors along the inclusion of the full
subcategory of `P` gives the functor `X ↦ (-, X)|_P`,
`P.restrictedPreadditiveYoneda : C ⥤ P.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat`. It sends a presentation
`A ⟶ B ⟶ X ⟶ 0` of `X` by objects of `P` to a presentation `(-, A) ⟶ (-, B) ⟶ (-, X)|_P ⟶ 0` of a
functor by representables, so the objects with such a presentation, `P.presented`, go to finitely
presented functors. This is an equivalence between `P.presented` and `mod P`, the Yoneda description
of the finitely presented functors on a category of projectives.

If moreover every object of `C` is a quotient of an object of `P`, every object of `C` is
`P`-presented and `C ≌ mod P`. In particular, an abelian category with enough projectives is
recovered from its projective objects as `mod (proj C)`.

## Main declarations

* `CategoryTheory.ObjectProperty.isFinitelyPresentedFunctor_restrictedPreadditiveYoneda_obj`: the
  restriction `(-, X)|_P` of a `P`-presented object `X` is a finitely presented functor on `P`.
* `CategoryTheory.ObjectProperty.exists_iso_restrictedPreadditiveYoneda_obj`: every finitely
  presented functor on `P` is `(-, X)|_P` for a `P`-presented object `X`.
* `CategoryTheory.ObjectProperty.equivalenceMod`: the equivalence between `P.presented` and
  `mod P`.
* `CategoryTheory.ObjectProperty.equivalenceModOfExistsEpi`: the equivalence `C ≌ mod P` when every
  object is a quotient of an object of `P`, and `TauCeti.equivalenceModProjectives`, the case
  `C ≌ mod (proj C)` of an abelian category with enough projectives.

## References

* M. Auslander, *Coherent functors*, Proceedings of the Conference on Categorical Algebra
  (La Jolla, 1965), Springer, 1966, 189-231.
-/

public section

universe v u

open CategoryTheory Limits Opposite TauCeti

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace ObjectProperty

variable [Abelian C] {P : ObjectProperty C}

/-- The restriction `(-, X)|_P` of a `P`-presented object is a finitely presented functor on `P`. -/
theorem isFinitelyPresentedFunctor_restrictedPreadditiveYoneda_obj (hP : P ≤ isProjective C)
    {X : C} (hX : P.presented X) :
    IsFinitelyPresentedFunctor (P.restrictedPreadditiveYoneda.obj X) := by
  obtain ⟨f, c, hc, hA, hB⟩ := hX
  let g : (⟨_, hA⟩ : P.FullSubcategory) ⟶ ⟨_, hB⟩ := P.homMk f
  have hc' : IsColimit (CokernelCofork.ofπ (f := g.hom) c.π c.condition) :=
    IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _))
  exact isFinitelyPresentedFunctor_iff_exists_isColimit.2
    ⟨_, _, g, _, _, ⟨isColimitRestrictedPreadditiveYoneda hP g hc'⟩⟩

/-- Every finitely presented functor on `P` is `(-, X)|_P` for a `P`-presented object `X`: the
cokernel of `(-, f)` is `(-, X)|_P` for `X` the cokernel of `f`. -/
theorem exists_iso_restrictedPreadditiveYoneda_obj (hP : P ≤ isProjective C)
    {F : P.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{v}} (hF : IsFinitelyPresentedFunctor F) :
    ∃ X, P.presented X ∧ Nonempty (P.restrictedPreadditiveYoneda.obj X ≅ F) := by
  obtain ⟨A, B, f, p, h, ⟨hc⟩⟩ := isFinitelyPresentedFunctor_iff_exists_isColimit.1 hF
  have hX := isColimitRestrictedPreadditiveYoneda hP f (w := cokernel.condition f.hom)
    (cokernelIsCokernel f.hom)
  have hf : MorphismProperty.ofObjectProperty P P f.hom := ⟨A.property, B.property⟩
  exact ⟨cokernel f.hom, (MorphismProperty.cokernels.of_isColimit f.hom _ (cokernelIsCokernel f.hom)
    hf :), ⟨hX.coconePointUniqueUpToIso hc⟩⟩

variable (P) in
/-- The functor `X ↦ (-, X)|_P` from a full subcategory `Q` of `P`-presented objects to `mod P`.
It is exposed so that `restrictedPreadditiveYonedaToMod_map_hom` has homogeneous types. -/
@[expose] def restrictedPreadditiveYonedaToMod (hP : P ≤ isProjective C) {Q : ObjectProperty C}
    (hQ : Q ≤ P.presented) :
    Q.FullSubcategory ⥤ (isFinitelyPresentedFunctor P.FullSubcategory).FullSubcategory :=
  ObjectProperty.lift _ (Q.ι ⋙ P.restrictedPreadditiveYoneda) fun X ↦
    isFinitelyPresentedFunctor_restrictedPreadditiveYoneda_obj hP (hQ _ X.property)

/-- The functor `restrictedPreadditiveYonedaToMod` sends `X` to `(-, X)|_P`. -/
@[simp]
theorem restrictedPreadditiveYonedaToMod_obj_obj (hP : P ≤ isProjective C) {Q : ObjectProperty C}
    (hQ : Q ≤ P.presented) (X : Q.FullSubcategory) :
    ((P.restrictedPreadditiveYonedaToMod hP hQ).obj X).obj =
      P.restrictedPreadditiveYoneda.obj X.obj :=
  rfl

/-- The functor `restrictedPreadditiveYonedaToMod` sends `f` to `(-, f)|_P`. -/
@[simp]
theorem restrictedPreadditiveYonedaToMod_map_hom (hP : P ≤ isProjective C) {Q : ObjectProperty C}
    (hQ : Q ≤ P.presented) {X Y : Q.FullSubcategory} (f : X ⟶ Y) :
    ((P.restrictedPreadditiveYonedaToMod hP hQ).map f).hom =
      P.restrictedPreadditiveYoneda.map f.hom :=
  rfl

instance (hP : P ≤ isProjective C) {Q : ObjectProperty C} (hQ : Q ≤ P.presented) :
    (P.restrictedPreadditiveYonedaToMod hP hQ).Faithful where
  map_injective {X Y f g} h := by
    refine ObjectProperty.hom_ext _ ((bijective_restrictedPreadditiveYoneda_map hP
      (hQ _ X.property) Y.obj).1 ?_)
    simpa using congr($(h).hom)

instance (hP : P ≤ isProjective C) {Q : ObjectProperty C} (hQ : Q ≤ P.presented) :
    (P.restrictedPreadditiveYonedaToMod hP hQ).Full where
  map_surjective {X Y} θ := by
    obtain ⟨g, hg⟩ := (bijective_restrictedPreadditiveYoneda_map hP
      (hQ _ X.property) Y.obj).2 θ.hom
    exact ⟨Q.homMk g, ObjectProperty.hom_ext _ (by simpa using hg)⟩

/-- The essential image of `X ↦ (-, X)|_P` is all of `mod P`. -/
theorem essSurj_restrictedPreadditiveYonedaToMod (hP : P ≤ isProjective C) {Q : ObjectProperty C}
    (hQ : Q = P.presented) : (P.restrictedPreadditiveYonedaToMod hP hQ.le).EssSurj where
  mem_essImage F := by
    obtain ⟨X, hX, ⟨e⟩⟩ := exists_iso_restrictedPreadditiveYoneda_obj hP F.property
    exact ⟨⟨X, hQ ▸ hX⟩, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- **The Yoneda description of `mod P`.** For a full subcategory `P` of projective objects of an
abelian category, the functor `X ↦ (-, X)|_P` is an equivalence from the objects with a
presentation by objects of `P`, given here as a property `Q` equal to `P.presented`, to the finitely
presented functors on `P`. -/
noncomputable def equivalenceMod (hP : P ≤ isProjective C) {Q : ObjectProperty C}
    (hQ : Q = P.presented) :
    Q.FullSubcategory ≌ (isFinitelyPresentedFunctor P.FullSubcategory).FullSubcategory :=
  have := essSurj_restrictedPreadditiveYonedaToMod hP hQ
  have : (P.restrictedPreadditiveYonedaToMod hP hQ.le).IsEquivalence := { }
  (P.restrictedPreadditiveYonedaToMod hP hQ.le).asEquivalence

/-- The functor of `equivalenceMod` is `X ↦ (-, X)|_P`. -/
noncomputable def equivalenceModCompιIso (hP : P ≤ isProjective C) {Q : ObjectProperty C}
    (hQ : Q = P.presented) :
    (equivalenceMod hP hQ).functor ⋙ (isFinitelyPresentedFunctor _).ι ≅
      Q.ι ⋙ P.restrictedPreadditiveYoneda :=
  Iso.refl _

/-- If `P` consists of projective objects and every object of the abelian category `C` is a quotient
of an object of `P`, then `X ↦ (-, X)|_P` is an equivalence from `C` to the finitely presented
functors on `P`. -/
noncomputable def equivalenceModOfExistsEpi (hP : P ≤ isProjective C)
    (hgen : ∀ X : C, ∃ (Q : C) (π : Q ⟶ X), P Q ∧ Epi π) :
    C ≌ (isFinitelyPresentedFunctor P.FullSubcategory).FullSubcategory :=
  (topEquivalence C).symm.trans (equivalenceMod hP (presented_eq_top hgen).symm)

/-- The functor of `equivalenceModOfExistsEpi` is `X ↦ (-, X)|_P`. -/
noncomputable def equivalenceModOfExistsEpiCompιIso (hP : P ≤ isProjective C)
    (hgen : ∀ X : C, ∃ (Q : C) (π : Q ⟶ X), P Q ∧ Epi π) :
    (equivalenceModOfExistsEpi hP hgen).functor ⋙ (isFinitelyPresentedFunctor _).ι ≅
      P.restrictedPreadditiveYoneda :=
  Iso.refl _

end ObjectProperty

end CategoryTheory

namespace TauCeti

variable (C : Type u) [Category.{v} C] [Abelian C] [EnoughProjectives C]

/-- An abelian category with enough projectives is equivalent to `mod (proj C)`, the finitely
presented functors on its full subcategory of projective objects, by `X ↦ (-, X)|_{proj C}`. -/
noncomputable def equivalenceModProjectives :
    C ≌ (isFinitelyPresentedFunctor (isProjective C).FullSubcategory).FullSubcategory :=
  ObjectProperty.equivalenceModOfExistsEpi le_rfl fun X ↦
    ⟨Projective.over X, Projective.π X, Projective.projective_over X, Projective.π_epi X⟩

/-- The functor of `equivalenceModProjectives` is `X ↦ (-, X)|_{proj C}`. -/
noncomputable def equivalenceModProjectivesCompιIso :
    (equivalenceModProjectives C).functor ⋙ (isFinitelyPresentedFunctor _).ι ≅
      (isProjective C).restrictedPreadditiveYoneda :=
  ObjectProperty.equivalenceModOfExistsEpiCompιIso _ _

end TauCeti
