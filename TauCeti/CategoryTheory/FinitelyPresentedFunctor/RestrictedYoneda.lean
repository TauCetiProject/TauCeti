/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.Basic

/-!
# Finitely presented functors on a subcategory of projective objects

Let `C` be an abelian category and let `P` be a property of objects of `C` satisfied only by
projective objects. Restricting representable functors along the inclusion of the full
subcategory of `P` gives the functor `X ↦ (-, X)|_P`,
`P.restrictedPreadditiveYoneda : C ⥤ P.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat`. Since `Hom(Q, -)` is
exact for `Q` projective, a presentation `A ⟶ B ⟶ X ⟶ 0` of `X` by objects of `P` becomes a
presentation `(-, A) ⟶ (-, B) ⟶ (-, X)|_P ⟶ 0` of a functor by representables, so the objects with
such a presentation, `P.presented`, go to finitely presented functors. This is an equivalence
between `P.presented` and `mod P`, the Yoneda description of the finitely presented functors on a
category of projectives.

If moreover every object of `C` is a quotient of an object of `P`, every object of `C` is
`P`-presented and `C ≌ mod P`. In particular, an abelian category with enough projectives is
recovered from its projective objects as `mod (proj C)`.

## Main declarations

* `CategoryTheory.ObjectProperty.restrictedPreadditiveYoneda`: the functor `X ↦ (-, X)|_P`.
* `CategoryTheory.ObjectProperty.presented`: the objects that are cokernels of morphisms between
  objects of `P`.
* `CategoryTheory.ObjectProperty.bijective_restrictedPreadditiveYoneda_map`: the functor
  `X ↦ (-, X)|_P` is fully faithful on morphisms out of a `P`-presented object.
* `CategoryTheory.ObjectProperty.exists_iso_restrictedPreadditiveYoneda_obj`: every finitely
  presented functor on `P` is `(-, X)|_P` for a `P`-presented object `X`.
* `CategoryTheory.ObjectProperty.presentedEquivalenceMod`: the equivalence between `P.presented`
  and `mod P`.
* `CategoryTheory.ObjectProperty.equivalenceMod`: the equivalence `C ≌ mod P` when every object is
  a quotient of an object of `P`, and `TauCeti.equivalenceModProjectives`, the case
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

section Preadditive

variable [Preadditive C] (P : ObjectProperty C)

/-- The functor `X ↦ (-, X)|_P`, restricting the representable functor `(-, X)` to the full
subcategory of `P`. -/
@[expose] def restrictedPreadditiveYoneda : C ⥤ P.FullSubcategoryᵒᵖ ⥤ AddCommGrpCat.{v} :=
  preadditiveYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj P.ι.op

/-- The natural transformation `(-, f)|_P` is postcomposition with `f`. -/
@[simp]
theorem restrictedPreadditiveYoneda_map_app_apply {X Y : C} (f : X ⟶ Y) (Q : P.FullSubcategoryᵒᵖ)
    (g : Q.unop.obj ⟶ X) : (P.restrictedPreadditiveYoneda.map f).app Q g = g ≫ f :=
  rfl

/-- The functor `(-, X)|_P` acts on morphisms of `P` by precomposition. -/
@[simp]
theorem restrictedPreadditiveYoneda_obj_map_apply (X : C) {Q Q' : P.FullSubcategoryᵒᵖ}
    (u : Q ⟶ Q') (g : Q.unop.obj ⟶ X) :
    (P.restrictedPreadditiveYoneda.obj X).map u g = u.unop.hom ≫ g :=
  rfl

instance : P.restrictedPreadditiveYoneda.Additive :=
  inferInstanceAs (preadditiveYoneda ⋙ _).Additive

/-- On the full subcategory of `P`, the functor `X ↦ (-, X)|_P` is the preadditive Yoneda
embedding. -/
def preadditiveYonedaIsoRestricted : preadditiveYoneda ≅ P.ι ⋙ P.restrictedPreadditiveYoneda :=
  NatIso.ofComponents (fun Y ↦ NatIso.ofComponents (fun Z ↦
    (InducedCategory.homAddEquiv (F := FullSubcategory.obj)).toAddCommGrpIso))

/-- The identification of `(-, Y)` with `(-, Y.obj)|_P` sends a morphism of the full subcategory to
the underlying morphism of `C`. -/
theorem preadditiveYonedaIsoRestricted_hom_app_app_apply (Y : P.FullSubcategory)
    (Z : P.FullSubcategoryᵒᵖ) (g : Z.unop ⟶ Y) :
    ((P.preadditiveYonedaIsoRestricted.hom.app Y).app Z) g = g.hom :=
  (rfl)

/-- The identification of `(-, Y)` with `(-, Y.obj)|_P` is natural in `Y`. -/
theorem preadditiveYoneda_map_comp_preadditiveYonedaIsoRestricted_hom {X Y : P.FullSubcategory}
    (f : X ⟶ Y) : preadditiveYoneda.map f ≫ P.preadditiveYonedaIsoRestricted.hom.app Y =
      P.preadditiveYonedaIsoRestricted.hom.app X ≫ P.restrictedPreadditiveYoneda.map f.hom :=
  P.preadditiveYonedaIsoRestricted.hom.naturality f

/-- The objects of `C` that are cokernels of morphisms between objects of `P`. -/
abbrev presented : ObjectProperty C :=
  (MorphismProperty.ofObjectProperty P P).cokernels

variable {P}

/-- Restriction to projective objects preserves epimorphisms. -/
theorem epi_map_restrictedPreadditiveYoneda (hP : P ≤ isProjective C) {X Y : C} (π : X ⟶ Y)
    [Epi π] : Epi (P.restrictedPreadditiveYoneda.map π) := by
  rw [NatTrans.epi_iff_epi_app]
  intro Q
  rw [AddCommGrpCat.epi_iff_surjective]
  intro (v : Q.unop.obj ⟶ Y)
  have : Projective Q.unop.obj := hP _ Q.unop.property
  exact ⟨Projective.factorThru (P := Q.unop.obj) v π,
    Projective.factorThru_comp (P := Q.unop.obj) v π⟩

/-- The functor `X ↦ (-, X)|_P` is fully faithful on morphisms out of a `P`-presented object: a
natural transformation `θ : (-, X)|_P ⟶ (-, Y)|_P` is `(-, g)` for the unique `g : X ⟶ Y` extending
`θ π : B ⟶ Y` along the epimorphism `π : B ⟶ X`, where `B` is an object of `P`. -/
theorem bijective_restrictedPreadditiveYoneda_map (hP : P ≤ isProjective C) {X : C}
    (hX : P.presented X) (Y : C) :
    Function.Bijective (P.restrictedPreadditiveYoneda.map : (X ⟶ Y) → _) := by
  obtain ⟨f, c, hc, hA, hB⟩ := hX
  have : Epi c.π := Cofork.IsColimit.epi hc
  let B : P.FullSubcategory := ⟨_, hB⟩
  constructor
  · intro g g' h
    rw [← cancel_epi c.π]
    exact congr($(h).app (op B) (c.π : B.obj ⟶ c.pt))
  · intro θ
    let t : B.obj ⟶ Y := θ.app (op B) c.π
    -- Naturality of `θ` says that `θ (u ≫ π) = u ≫ θ π` for `u` between objects of `P`.
    have hnat (Q : P.FullSubcategory) (u : Q.obj ⟶ B.obj) :
        θ.app (op Q) (u ≫ c.π) = u ≫ t :=
      NatTrans.naturality_apply θ (P.homMk u : Q ⟶ B).op (c.π : B.obj ⟶ c.pt)
    have hf : f ≫ t = 0 := by
      rw [← hnat ⟨_, hA⟩ f, CokernelCofork.condition]
      exact map_zero (θ.app (op ⟨_, hA⟩)).hom
    obtain ⟨g, hg⟩ := CokernelCofork.IsColimit.desc' hc t hf
    refine ⟨g, ?_⟩
    ext Q (u : Q.unop.obj ⟶ c.pt)
    have : Projective Q.unop.obj := hP _ Q.unop.property
    obtain ⟨v, rfl⟩ : ∃ v, v ≫ c.π = u :=
      ⟨_, Projective.factorThru_comp (P := Q.unop.obj) u c.π⟩
    simpa [hg] using (hnat Q.unop v).symm

end Preadditive

section Abelian

variable [Abelian C] {P : ObjectProperty C}

/-- Restriction to projective objects preserves exactness of short complexes. -/
theorem exact_map_restrictedPreadditiveYoneda (hP : P ≤ isProjective C) {S : ShortComplex C}
    (hS : S.Exact) : (S.map P.restrictedPreadditiveYoneda).Exact := by
  refine ShortComplex.exact_of_forall_evaluation _ fun Q ↦ ?_
  rw [ShortComplex.ab_exact_iff]
  intro (v : Q.unop.obj ⟶ S.X₂) hv
  have : Projective Q.unop.obj := hP _ Q.unop.property
  exact ⟨hS.liftFromProjective (P := Q.unop.obj) v hv,
    hS.liftFromProjective_comp (P := Q.unop.obj) v hv⟩

/-- A presentation `A ⟶ B ⟶ X ⟶ 0` by objects of `P`, which are projective, gives a presentation
`(-, A) ⟶ (-, B) ⟶ (-, X)|_P ⟶ 0` of `(-, X)|_P` by representable functors on `P`. -/
noncomputable def isColimitRestrictedPreadditiveYoneda (hP : P ≤ isProjective C)
    {A B : P.FullSubcategory} (f : A ⟶ B) {X : C} {π : B.obj ⟶ X} {w : f.hom ≫ π = 0}
    (hc : IsColimit (CokernelCofork.ofπ π w)) :
    IsColimit (CokernelCofork.ofπ (f := preadditiveYoneda.map f)
      (P.preadditiveYonedaIsoRestricted.hom.app B ≫ P.restrictedPreadditiveYoneda.map π) (by
        rw [reassoc_of% P.preadditiveYoneda_map_comp_preadditiveYonedaIsoRestricted_hom f,
          ← Functor.map_comp, w, Functor.map_zero, comp_zero])) := by
  have : Epi π := Cofork.IsColimit.epi hc
  let S : ShortComplex C := .mk f.hom π w
  have : Epi (S.map P.restrictedPreadditiveYoneda).g := epi_map_restrictedPreadditiveYoneda hP π
  have hS := exact_map_restrictedPreadditiveYoneda hP (ShortComplex.exact_of_g_is_cokernel S hc)
  refine CokernelCofork.isColimitOfIsColimitOfIff hS.gIsCokernel _
    (P.preadditiveYonedaIsoRestricted.app B) fun W φ ↦ ?_
  rw [Iso.app_hom, reassoc_of% P.preadditiveYoneda_map_comp_preadditiveYonedaIsoRestricted_hom f]
  exact (Preadditive.IsIso.comp_left_eq_zero _ _).symm

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

/-- If every object of `C` is a quotient of an object of `P`, then every object of `C` is a
cokernel of a morphism between objects of `P`. -/
theorem presented_eq_top (hgen : ∀ X : C, ∃ (Q : C) (π : Q ⟶ X), P Q ∧ Epi π) :
    P.presented = ⊤ := by
  refine top_le_iff.1 fun X _ ↦ ?_
  obtain ⟨B, π, hB, hπ⟩ := hgen X
  obtain ⟨A, e, hA, he⟩ := hgen (kernel π)
  let S : ShortComplex C := .mk (e ≫ kernel.ι π) π (by simp)
  have hS : S.Exact := by
    rw [S.exact_iff_epi_kernel_lift]
    convert he
    ext
    simp [S]
  have : Epi S.g := hπ
  exact .of_isColimit S.f _ hS.gIsCokernel ⟨hA, hB⟩

variable (P) in
/-- The functor `X ↦ (-, X)|_P` from a full subcategory `Q` of `P`-presented objects to `mod P`. -/
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

end Abelian

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
