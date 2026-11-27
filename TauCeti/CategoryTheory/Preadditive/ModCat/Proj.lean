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
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic
public import TauCeti.CategoryTheory.Preadditive.Projective.FiniteProducts

/-!
# Finitely generated projectives over a preadditive category

The finitely generated projective modules over a preadditive category `C` are precisely the
retracts of finite sums of representables. The extension of Yoneda to the matrix category
`Mat_ C` sends a finite family to the biproduct of its representables. Passing to the Karoubi
envelope yields an equivalence with the category of finitely generated projective modules.
For an idempotent-complete `C` with finite biproducts, Yoneda already gives the equivalence.

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
/-- The object property defining the category of finitely generated projective `C`-modules. -/
def proj : ObjectProperty (ModCat.{v} C) :=
  fun F ↦ Projective F ∧ IsFinitelyGeneratedFunctor F.obj

/-- Membership in `ModCat.proj C` means projectivity and finite generation. -/
@[simp]
theorem proj_iff {F : ModCat.{v} C} :
    proj C F ↔ Projective F ∧ IsFinitelyGeneratedFunctor F.obj :=
  Iff.rfl

instance (P : (proj C).FullSubcategory) : Projective P.obj :=
  (proj_iff.1 P.property).1

/-- The underlying functor of a finitely generated projective module is finitely generated. -/
theorem proj_isFinitelyGeneratedFunctor (P : (proj C).FullSubcategory) :
    IsFinitelyGeneratedFunctor P.obj.obj :=
  (proj_iff.1 P.property).2

private abbrev inclusion (C : Type u) [Category.{v} C] [Preadditive C] :=
  (additiveFunctor Cᵒᵖ AddCommGrpCat.{v}).ι

local instance : HasFiniteBiproducts (Cᵒᵖ ⥤ AddCommGrpCat.{v}) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The matrix extension of Yoneda has underlying functor the coproduct of the
representables indexed by the finite family. -/
def matLiftYonedaObjIsoCoproduct (X : Mat_ C) :
    ((Mat_.liftToBiproducts (yoneda C)).obj X).obj ≅ ∐ fun i ↦ preadditiveYoneda.obj (X.X i) :=
  (inclusion C).mapBiproduct _ ≪≫ biproduct.isoCoproduct _

/-- A module is finitely generated exactly when there is an epimorphism to it from the image
of a finite family under the matrix extension of Yoneda. -/
theorem isFinitelyGeneratedFunctor_iff_exists_epi_matLift {F : ModCat.{v} C} :
    IsFinitelyGeneratedFunctor F.obj ↔
      ∃ (X : Mat_ C) (p : (Mat_.liftToBiproducts (yoneda C)).obj X ⟶ F), Epi p := by
  rw [isFinitelyGeneratedFunctor_def]
  constructor
  · rintro ⟨n, Y, p, hp⟩
    let X : Mat_ C := ⟨Fin n, Y⟩
    let q : (Mat_.liftToBiproducts (yoneda C)).obj X ⟶ F :=
      ObjectProperty.homMk ((matLiftYonedaObjIsoCoproduct X).hom ≫ p)
    exact ⟨X, q, (inclusion C).epi_of_epi_map (epi_comp _ _)⟩
  · rintro ⟨X, p, hp⟩
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin X.ι
    let Y : Fin n → C := X.X ∘ e.symm
    let i := Sigma.reindex e.symm (fun j ↦ preadditiveYoneda.obj (X.X j))
    have : Epi ((inclusion C).map p) := (inclusion C).map_epi p
    exact ⟨n, Y, i.hom ≫ (matLiftYonedaObjIsoCoproduct X).inv ≫ (inclusion C).map p,
      epi_comp _ _⟩

private theorem proj_matLiftYoneda_obj (X : Mat_ C) :
    proj C ((Mat_.liftToBiproducts (yoneda C)).obj X) := by
  refine proj_iff.2 ⟨?_, isFinitelyGeneratedFunctor_iff_exists_epi_matLift.2
    ⟨X, 𝟙 _, inferInstance⟩⟩
  rw [Mat_.liftToBiproducts_obj]
  exact Projective.of_isColimit_cofan (biproduct.isColimit _)

/-- A finitely generated projective module is precisely a retract of a finite direct sum of
representables. The finite family may be empty. -/
theorem proj_iff_exists_retract_matLift {F : ModCat.{v} C} :
    proj C F ↔ ∃ X : Mat_ C, Nonempty (Retract F ((Mat_.liftToBiproducts (yoneda C)).obj X)) := by
  constructor
  · intro h
    obtain ⟨hP, hF⟩ := proj_iff.1 h
    obtain ⟨X, p, hp⟩ := isFinitelyGeneratedFunctor_iff_exists_epi_matLift.1 hF
    let : Projective F := hP
    obtain ⟨i, hi⟩ := Projective.factors (𝟙 F) p
    exact ⟨X, ⟨⟨i, p, hi⟩⟩⟩
  · rintro ⟨X, ⟨r⟩⟩
    let : Projective ((Mat_.liftToBiproducts (yoneda C)).obj X) :=
      (proj_iff.1 (proj_matLiftYoneda_obj X)).1
    exact proj_iff.2 ⟨r.projective,
      isFinitelyGeneratedFunctor_iff_exists_epi_matLift.2 ⟨X, r.r, inferInstance⟩⟩

/-- A projective module is finitely generated exactly when its underlying functor is
finitely presented. -/
theorem proj_iff_projective_and_isFinitelyPresentedFunctor {F : ModCat.{v} C} :
    proj C F ↔ Projective F ∧ IsFinitelyPresentedFunctor F.obj := by
  refine ⟨fun h ↦ ⟨(proj_iff.1 h).1, ?_⟩, fun h ↦
    proj_iff.2 ⟨h.1, h.2.isFinitelyGeneratedFunctor⟩⟩
  obtain ⟨X, ⟨r⟩⟩ := proj_iff_exists_retract_matLift.1 h
  let P : ObjectProperty (ModCat.{v} C) :=
    (isFinitelyPresentedFunctor C).inverseImage (inclusion C)
  have hX : P ((Mat_.liftToBiproducts (yoneda C)).obj X) := by
    rw [Mat_.liftToBiproducts_obj]
    exact P.prop_of_isLimit (biproduct.isLimit _)
      (fun i ↦ isFinitelyPresentedFunctor_preadditiveYoneda_obj (X.X i.as))
  exact P.prop_of_retract r hX

/-- Finitely generated projectives are closed under retracts. -/
instance : (proj C).IsStableUnderRetracts where
  of_retract r h := by
    obtain ⟨X, ⟨s⟩⟩ := proj_iff_exists_retract_matLift.1 h
    exact proj_iff_exists_retract_matLift.2 ⟨X, ⟨r.trans s⟩⟩

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
  (proj C).lift (Mat_.liftToBiproducts (yoneda C)) proj_matLiftYoneda_obj

private def matToProjFullyFaithful : (matToProj C).FullyFaithful :=
  let h := Mat_.fullyFaithfulLiftToBiproducts (Functor.FullyFaithful.ofFullyFaithful (yoneda C))
  let : (Mat_.liftToBiproducts (yoneda C)).Full := h.full
  let : (Mat_.liftToBiproducts (yoneda C)).Faithful := h.faithful
  Functor.FullyFaithful.ofFullyFaithful
    ((proj C).lift (Mat_.liftToBiproducts (yoneda C)) proj_matLiftYoneda_obj)

variable (C) in
/-- The Karoubi envelope of the matrix category is equivalent to the category of finitely
generated projective modules. This extends the assignment of a matrix-category object to the
finite direct sum of its representables. -/
def karoubiMatEquivProj : Karoubi (Mat_ C) ≌ (proj C).FullSubcategory := by
  let G := (functorExtension (Mat_ C) (proj C).FullSubcategory).obj (matToProj C)
  let hG : G.FullyFaithful := (matToProjFullyFaithful (C := C)).functorExtension
  let : G.Full := hG.full
  let : G.Faithful := hG.faithful
  let : G.EssSurj := ⟨fun P ↦ by
    rw [(matToProjFullyFaithful (C := C)).essImage_functorExtension]
    obtain ⟨X, ⟨r⟩⟩ := proj_iff_exists_retract_matLift.1 P.property
    refine ⟨(matToProj C).obj X, (matToProj C).obj_mem_essImage X, ⟨?_⟩⟩
    exact ⟨ObjectProperty.homMk r.i, ObjectProperty.homMk r.r,
      ObjectProperty.hom_ext _ r.retract⟩⟩
  let : G.IsEquivalence := {}
  exact G.asEquivalence

variable (C) in
/-- On the matrix category, the equivalence sends a finite family to the biproduct of
its representables and acts by the corresponding matrices of Yoneda maps. -/
def karoubiMatEquivProjRestrictIso :
    (toKaroubi (Mat_ C) ⋙ (karoubiMatEquivProj C).functor) ⋙ (proj C).ι ≅
      Mat_.liftToBiproducts (yoneda C) :=
  Functor.isoWhiskerRight (toKaroubiCompFunctorExtensionIso (matToProj C)) (proj C).ι ≪≫
    (proj C).liftCompιIso (Mat_.liftToBiproducts (yoneda C)) proj_matLiftYoneda_obj

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
      (proj_isFinitelyGeneratedFunctor P)
    let q : (yoneda C).obj Y ⟶ P.obj := ObjectProperty.homMk p
    let : Epi q := (inclusion C).epi_of_epi_map hp
    obtain ⟨i, hi⟩ := Projective.factors (𝟙 P.obj) q
    obtain ⟨X, ⟨e⟩⟩ := (yoneda C).essImage.prop_of_retract
      (Retract.mk i q hi) ((yoneda C).obj_mem_essImage Y)
    exact ⟨X, ⟨(proj C).fullyFaithfulι.preimageIso e⟩⟩⟩

end TauCeti.ModCat
