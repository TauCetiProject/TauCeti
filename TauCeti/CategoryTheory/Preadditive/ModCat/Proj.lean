/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Idempotents.FunctorExtension
public import TauCeti.CategoryTheory.ObjectProperty.FiniteProducts
public import TauCeti.CategoryTheory.ObjectProperty.FullSubcategory
public import TauCeti.CategoryTheory.Preadditive.Mat
public import TauCeti.CategoryTheory.Preadditive.ModCat.FiniteFree
public import TauCeti.CategoryTheory.Preadditive.Projective.FiniteProducts

/-!
# Finitely generated projectives over a preadditive category

The finitely generated projective modules over a preadditive category `C` are precisely the
retracts of finite sums of representables. The extension of Yoneda to the matrix category
`Mat_ C` sends a finite family to the biproduct of its representables. Passing to the Karoubi
envelope yields an equivalence with the category of finitely generated projective modules.
For an idempotent-complete `C` with finite biproducts, Yoneda already gives the equivalence.
If `C` has hom universe `v`, the ambient category is `ModCat.{v} C`, with the value
universe of Yoneda.

## References

* B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161, §1, pp. 10–12
  (idempotent and additive completions) and §3, pp. 17–18 (finite generation, finite free
  functors and the Yoneda description of the finitely generated projectives).
-/

public section

open CategoryTheory CategoryTheory.Idempotents Limits Opposite

noncomputable section

universe v u

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable (C) in
/-- The object property of finitely generated projectives in `ModCat.{v} C`, where `v` is
the hom universe of `C` and hence the value universe of Yoneda. -/
def proj : ObjectProperty (ModCat.{v} C) :=
  fun F ↦ Projective F ∧ IsFinitelyGeneratedFunctor F.obj

/-- Membership in `ModCat.proj C` means projectivity and finite generation. -/
@[simp]
theorem proj_iff {F : ModCat.{v} C} :
    proj C F ↔ Projective F ∧ IsFinitelyGeneratedFunctor F.obj :=
  Iff.rfl

/-- The underlying module of a finitely generated projective is projective in
the ambient category `ModCat.{v} C`. -/
instance (P : (proj C).FullSubcategory) : Projective P.obj :=
  (proj_iff.1 P.property).1

/-- The underlying functor of a finitely generated projective module is finitely generated. -/
theorem isFinitelyGeneratedFunctor_of_proj (P : (proj C).FullSubcategory) :
    IsFinitelyGeneratedFunctor P.obj.obj :=
  (proj_iff.1 P.property).2

private abbrev inclusion (C : Type u) [Category.{v} C] [Preadditive C] :=
  (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι

local instance : HasFiniteBiproducts (Cᵒᵖ ⥤ AddCommGrpCat.{v}) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end TauCeti.ModCat

namespace CategoryTheory.Mat_

open TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The matrix extension of Yoneda has underlying functor the coproduct of the
representables indexed by the finite family. -/
def liftToBiproductsYonedaObjIsoCoproduct (X : Mat_ C) :
    ((TauCeti.ModCat.yoneda C).liftToBiproducts.obj X).obj ≅
      ∐ fun i ↦ preadditiveYoneda.obj (X.X i) :=
  (inclusion C).mapIso ((TauCeti.ModCat.yoneda C).liftToBiproductsObjIso X) ≪≫
    (inclusion C).mapBiproduct _ ≪≫ biproduct.isoCoproduct _

/-- The Yoneda coproduct comparison sends each transported biproduct inclusion to the
corresponding coproduct injection. -/
@[reassoc (attr := simp)]
theorem map_ι_liftToBiproductsYonedaObjIsoCoproduct_hom (X : Mat_ C) (i : X.ι) :
    (biproduct.ι (fun j ↦ (TauCeti.ModCat.yoneda C).obj (X.X j)) i).hom ≫
      ((TauCeti.ModCat.yoneda C).liftToBiproductsObjIso X).inv.hom ≫
        X.liftToBiproductsYonedaObjIsoCoproduct.hom =
        Sigma.ι (fun j ↦ preadditiveYoneda.obj (X.X j)) i := by
  let F := fun j ↦ (TauCeti.ModCat.yoneda C).obj (X.X j)
  rw [← ObjectProperty.ι_map (f := biproduct.ι F i),
    ← ObjectProperty.ι_map (f := ((TauCeti.ModCat.yoneda C).liftToBiproductsObjIso X).inv),
    ← Functor.map_comp_assoc]
  simp only [liftToBiproductsYonedaObjIsoCoproduct, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc]
  have hi : (inclusion C).map (biproduct.ι F i) ≫ ((inclusion C).mapBiproduct F).hom =
      biproduct.ι ((inclusion C).obj ∘ F) i := by
    rw [← Iso.eq_comp_inv, Functor.mapBiproduct_inv, biproduct.ι_desc]
  rw [hi, biproduct.isoCoproduct_hom, biproduct.ι_desc]
  -- The underlying functors of the additive Yoneda objects are the representables.
  rfl

end CategoryTheory.Mat_

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable (C) in
/-- The finite free modules are the essential image of the matrix extension of Yoneda. -/
theorem isFiniteFree_eq_essImage_liftToBiproducts :
    isFiniteFree C = (yoneda C).liftToBiproducts.essImage := by
  ext F
  constructor
  · intro h
    obtain ⟨n, Y, ⟨e⟩⟩ := isFiniteFree_iff_exists_iso_biproduct.mp h
    let X : Mat_ C := ⟨Fin n, Y⟩
    exact ⟨X, ⟨(yoneda C).liftToBiproductsObjIso X ≪≫ e.symm⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    obtain ⟨n, ⟨i⟩⟩ := Finite.exists_equiv_fin X.ι
    exact isFiniteFree_iff_exists_iso_biproduct.mpr ⟨n, X.X ∘ i.symm,
      ⟨e.symm ≪≫ (yoneda C).liftToBiproductsObjIso X ≪≫
        (biproduct.reindex i.symm ((yoneda C).obj ∘ X.X)).symm⟩⟩

/-- A module is finitely generated exactly when it is a quotient of a finite free module. -/
theorem isFinitelyGeneratedFunctor_iff_exists_epi_finiteFree {F : ModCat.{v} C} :
    IsFinitelyGeneratedFunctor F.obj ↔
      ∃ (P : ModCat.{v} C) (_ : isFiniteFree C P) (p : P ⟶ F), Epi p := by
  rw [isFinitelyGeneratedFunctor_def]
  constructor
  · rintro ⟨n, Y, p, hp⟩
    let X : Mat_ C := ⟨Fin n, Y⟩
    let q : (yoneda C).liftToBiproducts.obj X ⟶ F :=
      ObjectProperty.homMk (X.liftToBiproductsYonedaObjIsoCoproduct.hom ≫ p)
    rw [isFiniteFree_eq_essImage_liftToBiproducts]
    exact ⟨_, (yoneda C).liftToBiproducts.obj_mem_essImage X, q,
      (inclusion C).epi_of_epi_map (epi_comp _ _)⟩
  · rintro ⟨P, hP, p, hp⟩
    rw [isFiniteFree_eq_essImage_liftToBiproducts] at hP
    obtain ⟨X, ⟨e⟩⟩ := hP
    obtain ⟨n, ⟨i⟩⟩ := Finite.exists_equiv_fin X.ι
    let s := Sigma.reindex i.symm (fun j ↦ preadditiveYoneda.obj (X.X j))
    have : Epi ((inclusion C).map (e.hom ≫ p)) := (inclusion C).map_epi _
    exact ⟨n, X.X ∘ i.symm, s.hom ≫ X.liftToBiproductsYonedaObjIsoCoproduct.inv ≫
      (inclusion C).map (e.hom ≫ p), epi_comp _ _⟩

/-- A finitely generated projective module is precisely a retract of a finite free module.
The finite family may be empty. -/
theorem proj_iff_exists_retract_finiteFree {F : ModCat.{v} C} :
    proj C F ↔ ∃ (P : ModCat.{v} C) (_ : isFiniteFree C P), Nonempty (Retract F P) := by
  constructor
  · intro h
    obtain ⟨hP, hF⟩ := proj_iff.1 h
    obtain ⟨P, h, p, hp⟩ := isFinitelyGeneratedFunctor_iff_exists_epi_finiteFree.1 hF
    obtain ⟨i, hi⟩ := Projective.factors (𝟙 F) p
    exact ⟨P, h, ⟨⟨i, p, hi⟩⟩⟩
  · rintro ⟨P, hP, ⟨r⟩⟩
    let : Projective P := projective_of_isFiniteFree hP
    exact proj_iff.2 ⟨r.projective,
      isFinitelyGeneratedFunctor_iff_exists_epi_finiteFree.2 ⟨P, hP, r.r, inferInstance⟩⟩

private theorem proj_liftToBiproducts_yoneda_obj (X : Mat_ C) :
    proj C ((yoneda C).liftToBiproducts.obj X) := by
  rw [proj_iff_exists_retract_finiteFree, isFiniteFree_eq_essImage_liftToBiproducts]
  exact ⟨_, (yoneda C).liftToBiproducts.obj_mem_essImage X, ⟨Retract.refl _⟩⟩

/-- A projective module is finitely generated exactly when its underlying functor is
finitely presented. -/
theorem proj_iff_projective_and_isFinitelyPresentedFunctor {F : ModCat.{v} C} :
    proj C F ↔ Projective F ∧ IsFinitelyPresentedFunctor F.obj := by
  refine ⟨fun h ↦ ⟨(proj_iff.1 h).1, ?_⟩, fun h ↦
    proj_iff.2 ⟨h.1, h.2.isFinitelyGeneratedFunctor⟩⟩
  obtain ⟨P, hP, ⟨r⟩⟩ := proj_iff_exists_retract_finiteFree.1 h
  exact ((isFinitelyPresentedFunctor C).inverseImage (inclusion C)).prop_of_retract r
    (isFinitelyPresentedFunctor_of_isFiniteFree hP)

/-- Finitely generated projectives are closed under retracts. -/
instance : (proj C).IsStableUnderRetracts where
  of_retract r h := by
    obtain ⟨P, hP, ⟨s⟩⟩ := proj_iff_exists_retract_finiteFree.1 h
    exact proj_iff_exists_retract_finiteFree.2 ⟨P, hP, ⟨r.trans s⟩⟩

/-- Finitely generated projectives are closed under finite products. In `Mod C` these are
also finite coproducts. -/
instance : (proj C).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    let P := (isFinitelyPresentedFunctor C).inverseImage (inclusion C)
    refine ⟨fun X ⟨hX⟩ ↦ proj_iff_projective_and_isFinitelyPresentedFunctor.2 ⟨?_, ?_⟩⟩
    · exact (hX.ofLE fun _ h ↦ (proj_iff.1 h).1 : (isProjective _).LimitOfShape _ X).prop
    · exact (hX.ofLE fun _ h ↦
        (proj_iff_projective_and_isFinitelyPresentedFunctor.1 h).2 : P.LimitOfShape _ X).prop

variable (C) in
/-- Yoneda with codomain the finitely generated projectives. -/
abbrev projYoneda : C ⥤ (proj C).FullSubcategory :=
  (proj C).lift (yoneda C) fun X ↦ proj_iff.2
    ⟨inferInstance, isFinitelyGeneratedFunctor_preadditiveYoneda_obj X⟩

private def matToProj (C : Type u) [Category.{v} C] [Preadditive C] :
    Mat_ C ⥤ (proj C).FullSubcategory :=
  (proj C).lift ((yoneda C).liftToBiproducts) proj_liftToBiproducts_yoneda_obj

private def matToProjFullyFaithful : (matToProj C).FullyFaithful :=
  let h := (Functor.FullyFaithful.ofFullyFaithful (yoneda C)).liftToBiproducts
  let : ((yoneda C).liftToBiproducts).Full := h.full
  let : ((yoneda C).liftToBiproducts).Faithful := h.faithful
  Functor.FullyFaithful.ofFullyFaithful
    ((proj C).lift ((yoneda C).liftToBiproducts) proj_liftToBiproducts_yoneda_obj)

variable (C) in
/-- The Karoubi envelope of the matrix category is equivalent to the category of finitely
generated projective modules. On objects embedded by `toKaroubi`, the forward functor recovers
the finite sum of representables up to `karoubiMatEquivProjRestrictIso` after inclusion into the
ambient module category. -/
def karoubiMatEquivProj : Karoubi (Mat_ C) ≌ (proj C).FullSubcategory := by
  let G := (functorExtension (Mat_ C) (proj C).FullSubcategory).obj (matToProj C)
  let hG : G.FullyFaithful := (matToProjFullyFaithful (C := C)).functorExtension
  let : G.Full := hG.full
  let : G.Faithful := hG.faithful
  let : G.EssSurj := ⟨fun P ↦ by
    rw [(matToProjFullyFaithful (C := C)).essImage_functorExtension]
    obtain ⟨Q, hQ, ⟨r⟩⟩ := proj_iff_exists_retract_finiteFree.1 P.property
    rw [isFiniteFree_eq_essImage_liftToBiproducts] at hQ
    obtain ⟨X, ⟨e⟩⟩ := hQ
    let r' := r.trans e.symm.retract
    refine ⟨(matToProj C).obj X, (matToProj C).obj_mem_essImage X, ⟨?_⟩⟩
    exact ⟨ObjectProperty.homMk r'.i, ObjectProperty.homMk r'.r,
      ObjectProperty.hom_ext _ r'.retract⟩⟩
  let : G.IsEquivalence := {}
  exact G.asEquivalence

variable (C) in
/-- Restricting the equivalence along `toKaroubi` and including into the ambient module
category gives a functor naturally isomorphic to the biproduct extension of Yoneda. -/
def karoubiMatEquivProjRestrictIso :
    (toKaroubi (Mat_ C) ⋙ (karoubiMatEquivProj C).functor) ⋙ (proj C).ι ≅
      (yoneda C).liftToBiproducts :=
  Functor.isoWhiskerRight ((matToProj C).toKaroubiCompFunctorExtensionIso) (proj C).ι ≪≫
    (proj C).liftCompιIso ((yoneda C).liftToBiproducts) proj_liftToBiproducts_yoneda_obj

variable (C) in
/-- The category of finitely generated projective modules is equivalent to
`Karoubi (Mat_ C)`. -/
theorem nonempty_projEquivKaroubiMat :
    Nonempty ((proj C).FullSubcategory ≌ Karoubi (Mat_ C)) :=
  ⟨(karoubiMatEquivProj C).symm⟩

/-- When the source has finite biproducts and split idempotents, every finitely generated
projective module is representable. -/
instance [HasFiniteBiproducts C] [IsIdempotentComplete C] : (projYoneda C).IsEquivalence where
  essSurj := ⟨fun P ↦ by
    obtain ⟨Y, p, hp⟩ := (isFinitelyGeneratedFunctor_iff_exists_single _).1
      (isFinitelyGeneratedFunctor_of_proj P)
    let q : (yoneda C).obj Y ⟶ P.obj := ObjectProperty.homMk p
    let : Epi q := (inclusion C).epi_of_epi_map hp
    obtain ⟨i, hi⟩ := Projective.factors (𝟙 P.obj) q
    obtain ⟨X, ⟨e⟩⟩ := (yoneda C).essImage.prop_of_retract
      (Retract.mk i q hi) ((yoneda C).obj_mem_essImage Y)
    exact ⟨X, ⟨(proj C).fullyFaithfulι.preimageIso e⟩⟩⟩

end TauCeti.ModCat

namespace CategoryTheory.Idempotents.Karoubi

open TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The image of a formal summand is a retract of the matrix lift of its underlying object.
The maps are obtained from the Karoubi summand maps via the restriction isomorphism. -/
def matEquivProjRetract (P : Karoubi (Mat_ C)) :
    Retract ((karoubiMatEquivProj C).functor.obj P).obj
      ((TauCeti.ModCat.yoneda C).liftToBiproducts.obj P.X) :=
  (P.retract.map ((karoubiMatEquivProj C).functor ⋙ (proj C).ι)).trans
    ((karoubiMatEquivProjRestrictIso C).app P.X).retract

/-- The inclusion of the retract is the mapped Karoubi inclusion followed by the restriction
isomorphism. -/
theorem matEquivProjRetract_i (P : Karoubi (Mat_ C)) :
    (matEquivProjRetract P).i =
      ((karoubiMatEquivProj C).functor ⋙ (proj C).ι).map P.decompId_i ≫
        (karoubiMatEquivProjRestrictIso C).hom.app P.X := by
  have hi : P.retract.i = P.decompId_i := by
    apply Karoubi.hom_ext
    simp
  simp only [matEquivProjRetract, Retract.trans_i, Retract.map_i, Iso.retract_i, Iso.app_hom, hi]

/-- The projection of the retract is the inverse restriction isomorphism followed by the mapped
Karoubi projection. -/
theorem matEquivProjRetract_r (P : Karoubi (Mat_ C)) :
    (matEquivProjRetract P).r =
      (karoubiMatEquivProjRestrictIso C).inv.app P.X ≫
        ((karoubiMatEquivProj C).functor ⋙ (proj C).ι).map P.decompId_p := by
  have hr : P.retract.r = P.decompId_p := by
    apply Karoubi.hom_ext
    simp
  simp only [matEquivProjRetract, Retract.trans_r, Retract.map_r, Iso.retract_r, Iso.app_inv, hr]

/-- The other composite of the retract maps is the image of the matrix idempotent. -/
@[reassoc (attr := simp)]
theorem matEquivProjRetract_r_i (P : Karoubi (Mat_ C)) :
    (matEquivProjRetract P).r ≫ (matEquivProjRetract P).i =
      (TauCeti.ModCat.yoneda C).liftToBiproducts.map P.p := by
  rw [matEquivProjRetract_r, matEquivProjRetract_i]
  rw [Category.assoc, ← Functor.map_comp_assoc, ← P.decomp_p]
  have h := (karoubiMatEquivProjRestrictIso C).hom.naturality P.p
  simp only [Functor.comp_map] at h ⊢
  rw [h, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Idempotents.Karoubi
