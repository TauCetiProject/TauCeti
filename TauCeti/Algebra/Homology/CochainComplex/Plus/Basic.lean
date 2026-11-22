/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.SingleHomology

/-!
# Single complexes, mapping cones, truncations, and composition on `CochainComplex.Plus`

This file provides general constructions on Mathlib's category `CochainComplex.Plus C` of
bounded-below `ℤ`-indexed cochain complexes under minimal categorical hypotheses:

* `TauCeti.CochainComplex.Plus.singleFunctor` and `singleFunctorCompιIso`: the single-object
  embedding `C ⥤ CochainComplex.Plus C` in degree `n : ℤ` (for `[HasZeroMorphisms C]` and
  `[HasZeroObject C]`).
* `CochainComplex.Plus.mappingCone`, `mappingConeTriangle`, and
  `mappingConeTriangleιIso`: mapping cones and mapping cone triangles in `CochainComplex.Plus C`
  (for `[Preadditive C]` and `[HasBinaryBiproducts C]`).
* `CochainComplex.Plus.truncLE`, `truncGE`, `truncLEMap`, `truncGEMap`, `ιTruncLE`, and
  `πTruncGE`: canonical functorial truncations on `CochainComplex.Plus C` together with their
  naturality laws and `QuasiIso` instances under `IsLE`/`IsGE` (for `[HasZeroMorphisms C]`,
  `[HasZeroObject C]`, and `[∀ i, K.obj.HasHomology i]`).
* `CategoryTheory.Functor.mapCochainComplexPlusCompIso` (with its `NatTrans.CommShift` instance)
  and `CategoryTheory.NatTrans.isIso_mapCochainComplexPlus`: functoriality of
  `Functor.mapCochainComplexPlus` with respect to composition and natural isomorphisms.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace TauCeti.CochainComplex.Plus

section Single

variable (C : Type u₁) [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The functor `C ⥤ CochainComplex.Plus C` sending `X` to the cochain complex concentrated in
degree `n : ℤ`. -/
@[implicit_reducible]
def singleFunctor (n : ℤ) : C ⥤ _root_.CochainComplex.Plus C :=
  ObjectProperty.lift _ (HomologicalComplex.single C (.up ℤ) n)
    (fun _ ↦ ⟨n, inferInstance⟩)

/-- Inclusion into `CochainComplex C ℤ` identifies `singleFunctor C n` with
`HomologicalComplex.single C (.up ℤ) n`. -/
def singleFunctorCompιIso (n : ℤ) :
    singleFunctor C n ⋙ _root_.CochainComplex.Plus.ι C ≅
      HomologicalComplex.single C (.up ℤ) n :=
  ObjectProperty.liftCompιIso _ _ _

variable {C}

/-- The underlying cochain complex of `(singleFunctor C n).obj X` is
`(HomologicalComplex.single C (.up ℤ) n).obj X`. -/
@[simp]
lemma singleFunctor_obj_obj (n : ℤ) (X : C) :
    ((singleFunctor C n).obj X).obj = (HomologicalComplex.single C (.up ℤ) n).obj X :=
  (rfl)

/-- Component formula for `(singleFunctorCompιIso C n).hom` at `X`. -/
@[simp]
lemma singleFunctorCompιIso_hom_app (n : ℤ) (X : C) :
    (singleFunctorCompιIso C n).hom.app X = eqToHom (singleFunctor_obj_obj n X) :=
  (rfl)

/-- Component formula for `(singleFunctorCompιIso C n).inv` at `X`. -/
@[simp]
lemma singleFunctorCompιIso_inv_app (n : ℤ) (X : C) :
    (singleFunctorCompιIso C n).inv.app X = eqToHom (singleFunctor_obj_obj n X).symm :=
  (rfl)

/-- Component formula for `(singleFunctor C n).map f`. -/
@[simp]
lemma singleFunctor_map_hom (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    ((singleFunctor C n).map f).hom =
      eqToHom (singleFunctor_obj_obj n X) ≫
        (HomologicalComplex.single C (.up ℤ) n).map f ≫
        eqToHom (singleFunctor_obj_obj n Y).symm := by
  have h := (singleFunctorCompιIso C n).hom.naturality f
  simp only [Functor.comp_map, ObjectProperty.ι_map, singleFunctorCompιIso_hom_app] at h
  simpa [Category.assoc] using congrArg (· ≫ eqToHom (singleFunctor_obj_obj n Y).symm) h

instance hasHomology_singleFunctor_obj (n : ℤ) (X : C) (i : ℤ) :
    ((singleFunctor C n).obj X).obj.HasHomology i :=
  HomologicalComplex.hasHomology_of_iso (eqToIso (singleFunctor_obj_obj n X)).symm i

end Single

end TauCeti.CochainComplex.Plus

namespace CochainComplex.Plus

section MappingCone

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The mapping cone of a morphism `f : K ⟶ L` in `CochainComplex.Plus C`, as a bounded-below
cochain complex. -/
def mappingCone {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    CochainComplex.Plus C :=
  ⟨_root_.CochainComplex.mappingCone f.hom, by
    obtain ⟨n₁, _⟩ := K.property
    obtain ⟨n₂, _⟩ := L.property
    exact ⟨min (n₁ - 1) n₂, _root_.CochainComplex.isStrictlyGE_mappingCone f.hom n₁ n₂
      (min (n₁ - 1) n₂) (by omega) (by omega)⟩⟩

/-- The underlying cochain complex of `mappingCone f` is
`_root_.CochainComplex.mappingCone f.hom`. -/
@[simp]
lemma mappingCone_obj {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingCone f).obj = _root_.CochainComplex.mappingCone f.hom :=
  (rfl)

/-- The mapping cone triangle `K ⟶ L ⟶ cone(f) ⟶ K⟦1⟧` in `CochainComplex.Plus C`. -/
def mappingConeTriangle {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    Triangle (CochainComplex.Plus C) :=
  Triangle.mk f
    (ObjectProperty.homMk
      (_root_.CochainComplex.mappingCone.inr f.hom ≫ eqToHom (mappingCone_obj f).symm) :
      L ⟶ mappingCone f)
    ((CochainComplex.Plus.fullyFaithfulι C).preimage
      (eqToHom (mappingCone_obj f) ≫
        (_root_.CochainComplex.mappingCone.triangle f.hom).mor₃ ≫
        ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).inv.app K))

/-- First vertex of `mappingConeTriangle f`. -/
@[simp]
lemma mappingConeTriangle_obj₁ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).obj₁ = K :=
  (rfl)

/-- Second vertex of `mappingConeTriangle f`. -/
@[simp]
lemma mappingConeTriangle_obj₂ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).obj₂ = L :=
  (rfl)

/-- Third vertex of `mappingConeTriangle f`. -/
@[simp]
lemma mappingConeTriangle_obj₃ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).obj₃ = mappingCone f :=
  (rfl)

/-- First morphism of `mappingConeTriangle f`. -/
@[simp]
lemma mappingConeTriangle_mor₁ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).mor₁ =
      eqToHom (mappingConeTriangle_obj₁ f) ≫ f ≫
        eqToHom (mappingConeTriangle_obj₂ f).symm :=
  (conj_eqToHom_iff_heq _ _ _ (mappingConeTriangle_obj₂ f)).2 HEq.rfl

/-- Second morphism of `mappingConeTriangle f` on underlying cochain complexes. -/
@[simp]
lemma mappingConeTriangle_mor₂_hom {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).mor₂.hom =
      eqToHom (congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₂ f)) ≫
        _root_.CochainComplex.mappingCone.inr f.hom ≫
        eqToHom ((congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₃ f)).trans
          (mappingCone_obj f)).symm := by
  refine (conj_eqToHom_iff_heq _ _
    (congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₂ f))
    ((congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₃ f)).trans
      (mappingCone_obj f))).2 ?_
  have h : (mappingConeTriangle f).mor₂.hom ≍
      _root_.CochainComplex.mappingCone.inr f.hom ≫ eqToHom (mappingCone_obj f).symm := HEq.rfl
  have h' : _root_.CochainComplex.mappingCone.inr f.hom ≫ eqToHom (mappingCone_obj f).symm ≍
      _root_.CochainComplex.mappingCone.inr f.hom :=
    (conj_eqToHom_iff_heq _ _ rfl (mappingCone_obj f)).1 (by simp)
  exact h.trans h'

/-- Third morphism of `mappingConeTriangle f`. -/
lemma mappingConeTriangle_mor₃ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).mor₃ =
      eqToHom (mappingConeTriangle_obj₃ f) ≫
        (CochainComplex.Plus.fullyFaithfulι C).preimage
          (eqToHom (mappingCone_obj f) ≫
            (_root_.CochainComplex.mappingCone.triangle f.hom).mor₃ ≫
            ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).inv.app K) ≫
        eqToHom (congrArg (·⟦(1 : ℤ)⟧) (mappingConeTriangle_obj₁ f)).symm :=
  (conj_eqToHom_iff_heq _ _ _
    (congrArg (·⟦(1 : ℤ)⟧) (mappingConeTriangle_obj₁ f))).2 HEq.rfl

/-- Third morphism of `mappingConeTriangle f` on underlying cochain complexes. -/
@[simp]
lemma mappingConeTriangle_mor₃_hom {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).mor₃.hom =
      eqToHom ((congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₃ f)).trans
          (mappingCone_obj f)) ≫
        (_root_.CochainComplex.mappingCone.triangle f.hom).mor₃ ≫
        ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).inv.app K ≫
        eqToHom
          (congrArg (fun X ↦ (X⟦(1 : ℤ)⟧).obj) (mappingConeTriangle_obj₁ f)).symm := by
  have h := (CochainComplex.Plus.fullyFaithfulι C).map_preimage
    (X := mappingCone f) (Y := K⟦(1 : ℤ)⟧)
    (eqToHom (mappingCone_obj f) ≫
      (_root_.CochainComplex.mappingCone.triangle f.hom).mor₃ ≫
      ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).inv.app K)
  simp only [ObjectProperty.ι_map] at h
  rw [mappingConeTriangle_mor₃]
  simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom]
  rw [h]
  simp

/-- Characterizing equation for the connecting morphism of `mappingConeTriangle f` after inclusion
into `CochainComplex C ℤ`. -/
@[reassoc]
lemma mappingConeTriangle_mor₃_hom_comp {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).mor₃.hom ≫
        eqToHom (congrArg (fun X ↦ (X⟦(1 : ℤ)⟧).obj) (mappingConeTriangle_obj₁ f)) ≫
        ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).hom.app K =
      eqToHom ((congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₃ f)).trans
          (mappingCone_obj f)) ≫
        (_root_.CochainComplex.mappingCone.triangle f.hom).mor₃ := by
  rw [mappingConeTriangle_mor₃_hom]
  simp

/-- Inclusion into `CochainComplex C ℤ` identifies `mappingConeTriangle f` with
`CochainComplex.mappingCone.triangle f.hom`. -/
def mappingConeTriangleιIso {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (CochainComplex.Plus.ι C).mapTriangle.obj (mappingConeTriangle f) ≅
      _root_.CochainComplex.mappingCone.triangle f.hom :=
  Triangle.isoMk _ _
    (eqToIso (congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₁ f)))
    (eqToIso (congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₂ f)))
    (eqToIso ((congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₃ f)).trans
      (mappingCone_obj f)))
    (by
      simp [Functor.mapTriangle_obj, mappingConeTriangle_mor₁])
    (by
      simp [Functor.mapTriangle_obj, mappingConeTriangle_mor₂_hom])
    (by
      simp only [Functor.mapTriangle_obj, Triangle.mk_mor₃, Triangle.mk_obj₁,
        ObjectProperty.ι_map, eqToIso.hom, Category.assoc]
      have hshift :
          eqToHom (congrArg (fun X ↦ (X⟦(1 : ℤ)⟧).obj) (mappingConeTriangle_obj₁ f)) ≫
            ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).hom.app K =
          ((CochainComplex.Plus.ι C).commShiftIso (1 : ℤ)).hom.app
              (mappingConeTriangle f).obj₁ ≫
            (eqToHom (congrArg ObjectProperty.FullSubcategory.obj
              (mappingConeTriangle_obj₁ f)))⟦(1 : ℤ)⟧' := by
        simp [eqToHom_map]
      rw [← hshift, mappingConeTriangle_mor₃_hom_comp])

@[simp]
lemma mappingConeTriangleιIso_hom_hom₁ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).hom.hom₁ =
      eqToHom (congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₁ f)) :=
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_hom_hom₂ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).hom.hom₂ =
      eqToHom (congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₂ f)) :=
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_hom_hom₃ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).hom.hom₃ =
      eqToHom ((congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₃ f)).trans
        (mappingCone_obj f)) :=
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_inv_hom₁ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).inv.hom₁ =
      eqToHom (congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₁ f)).symm :=
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_inv_hom₂ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).inv.hom₂ =
      eqToHom (congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₂ f)).symm :=
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_inv_hom₃ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).inv.hom₃ =
      eqToHom ((congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₃ f)).trans
        (mappingCone_obj f)).symm :=
  (rfl)

end MappingCone

section Trunc

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The canonical `≤ n` truncation of a bounded-below cochain complex stays bounded below. -/
def truncLE (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    CochainComplex.Plus C :=
  ⟨K.obj.truncLE n, by
    obtain ⟨b, _⟩ := K.property
    exact ⟨b, inferInstance⟩⟩

/-- The canonical `≥ n` truncation of a bounded-below cochain complex stays bounded below. -/
def truncGE (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    CochainComplex.Plus C :=
  ⟨K.obj.truncGE n, by
    obtain ⟨b, _⟩ := K.property
    exact ⟨b, inferInstance⟩⟩

/-- The underlying cochain complex of `K.truncLE n` is `K.obj.truncLE n`. -/
@[simp]
lemma truncLE_obj (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    (K.truncLE n).obj = K.obj.truncLE n :=
  (rfl)

/-- The underlying cochain complex of `K.truncGE n` is `K.obj.truncGE n`. -/
@[simp]
lemma truncGE_obj (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    (K.truncGE n).obj = K.obj.truncGE n :=
  (rfl)

instance hasHomology_truncLE (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]
    (n i : ℤ) : (K.truncLE n).obj.HasHomology i :=
  HomologicalComplex.hasHomology_of_iso (eqToIso (K.truncLE_obj n)).symm i

instance hasHomology_truncGE (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]
    (n i : ℤ) : (K.truncGE n).obj.HasHomology i :=
  HomologicalComplex.hasHomology_of_iso (eqToIso (K.truncGE_obj n)).symm i

instance isStrictlyLE_truncLE_obj (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]
    (n : ℤ) : (K.truncLE n).obj.IsStrictlyLE n := by
  rw [truncLE_obj]
  infer_instance

instance isStrictlyGE_truncGE_obj (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]
    (n : ℤ) : (K.truncGE n).obj.IsStrictlyGE n := by
  rw [truncGE_obj]
  infer_instance

/-- The canonical morphism `τ_{≤ n} K ⟶ K` in `CochainComplex.Plus C`. -/
def ιTruncLE (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    K.truncLE n ⟶ K :=
  ObjectProperty.homMk (eqToHom (K.truncLE_obj n) ≫ K.obj.ιTruncLE n)

/-- The canonical morphism `K ⟶ τ_{≥ n} K` in `CochainComplex.Plus C`. -/
def πTruncGE (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    K ⟶ K.truncGE n :=
  ObjectProperty.homMk (K.obj.πTruncGE n ≫ eqToHom (K.truncGE_obj n).symm)

/-- Underlying cochain-complex morphism of `K.ιTruncLE n`. -/
@[simp]
lemma ιTruncLE_hom (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    (K.ιTruncLE n).hom = eqToHom (K.truncLE_obj n) ≫ K.obj.ιTruncLE n := by
  simp [ιTruncLE]

/-- Underlying cochain-complex morphism of `K.πTruncGE n`. -/
@[simp]
lemma πTruncGE_hom (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    (K.πTruncGE n).hom = K.obj.πTruncGE n ≫ eqToHom (K.truncGE_obj n).symm := by
  simp [πTruncGE]

instance quasiIso_ιTruncLE_hom (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]
    (n : ℤ) [K.obj.IsLE n] : QuasiIso (K.ιTruncLE n).hom := by
  rw [ιTruncLE_hom]
  infer_instance

instance quasiIso_πTruncGE_hom (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i]
    (n : ℤ) [K.obj.IsGE n] : QuasiIso (K.πTruncGE n).hom := by
  rw [πTruncGE_hom]
  infer_instance

/-- The morphism `K.truncLE n ⟶ L.truncLE n` induced by a morphism `f : K ⟶ L` in
`CochainComplex.Plus C`. -/
def truncLEMap {K L : CochainComplex.Plus C} [∀ i, K.obj.HasHomology i]
    [∀ i, L.obj.HasHomology i] (f : K ⟶ L) (n : ℤ) :
    K.truncLE n ⟶ L.truncLE n :=
  ObjectProperty.homMk
    (eqToHom (K.truncLE_obj n) ≫
      _root_.CochainComplex.truncLEMap f.hom n ≫
      eqToHom (L.truncLE_obj n).symm)

/-- The morphism `K.truncGE n ⟶ L.truncGE n` induced by a morphism `f : K ⟶ L` in
`CochainComplex.Plus C`. -/
def truncGEMap {K L : CochainComplex.Plus C} [∀ i, K.obj.HasHomology i]
    [∀ i, L.obj.HasHomology i] (f : K ⟶ L) (n : ℤ) :
    K.truncGE n ⟶ L.truncGE n :=
  ObjectProperty.homMk
    (eqToHom (K.truncGE_obj n) ≫
      _root_.CochainComplex.truncGEMap f.hom n ≫
      eqToHom (L.truncGE_obj n).symm)

/-- Underlying cochain-complex morphism of `truncLEMap f n`. -/
@[simp]
lemma truncLEMap_hom {K L : CochainComplex.Plus C} [∀ i, K.obj.HasHomology i]
    [∀ i, L.obj.HasHomology i] (f : K ⟶ L) (n : ℤ) :
    (truncLEMap f n).hom =
      eqToHom (K.truncLE_obj n) ≫
        _root_.CochainComplex.truncLEMap f.hom n ≫
        eqToHom (L.truncLE_obj n).symm := by
  simp [truncLEMap]

/-- Underlying cochain-complex morphism of `truncGEMap f n`. -/
@[simp]
lemma truncGEMap_hom {K L : CochainComplex.Plus C} [∀ i, K.obj.HasHomology i]
    [∀ i, L.obj.HasHomology i] (f : K ⟶ L) (n : ℤ) :
    (truncGEMap f n).hom =
      eqToHom (K.truncGE_obj n) ≫
        _root_.CochainComplex.truncGEMap f.hom n ≫
        eqToHom (L.truncGE_obj n).symm := by
  simp [truncGEMap]

/-- `truncLEMap` sends the identity morphism to the identity. -/
@[simp]
lemma truncLEMap_id (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    truncLEMap (𝟙 K) n = 𝟙 (K.truncLE n) := by
  ext1
  simp [HomologicalComplex.truncLEMap_id]

/-- `truncLEMap` preserves composition. -/
@[simp, reassoc]
lemma truncLEMap_comp {K L M : CochainComplex.Plus C} [∀ i, K.obj.HasHomology i]
    [∀ i, L.obj.HasHomology i] [∀ i, M.obj.HasHomology i]
    (f : K ⟶ L) (g : L ⟶ M) (n : ℤ) :
    truncLEMap (f ≫ g) n = truncLEMap f n ≫ truncLEMap g n := by
  ext1
  simp [HomologicalComplex.truncLEMap_comp]

/-- `truncGEMap` sends the identity morphism to the identity. -/
@[simp]
lemma truncGEMap_id (K : CochainComplex.Plus C) [∀ i, K.obj.HasHomology i] (n : ℤ) :
    truncGEMap (𝟙 K) n = 𝟙 (K.truncGE n) := by
  ext1
  simp [HomologicalComplex.truncGEMap_id]

/-- `truncGEMap` preserves composition. -/
@[simp, reassoc]
lemma truncGEMap_comp {K L M : CochainComplex.Plus C} [∀ i, K.obj.HasHomology i]
    [∀ i, L.obj.HasHomology i] [∀ i, M.obj.HasHomology i]
    (f : K ⟶ L) (g : L ⟶ M) (n : ℤ) :
    truncGEMap (f ≫ g) n = truncGEMap f n ≫ truncGEMap g n := by
  ext1
  simp [HomologicalComplex.truncGEMap_comp]

/-- Naturality of `ιTruncLE` in `CochainComplex.Plus C`. -/
@[reassoc (attr := simp)]
lemma ιTruncLE_naturality {K L : CochainComplex.Plus C} [∀ i, K.obj.HasHomology i]
    [∀ i, L.obj.HasHomology i] (f : K ⟶ L) (n : ℤ) :
    truncLEMap f n ≫ L.ιTruncLE n = K.ιTruncLE n ≫ f := by
  ext1
  simp

/-- Naturality of `πTruncGE` in `CochainComplex.Plus C`. -/
@[reassoc (attr := simp)]
lemma πTruncGE_naturality {K L : CochainComplex.Plus C} [∀ i, K.obj.HasHomology i]
    [∀ i, L.obj.HasHomology i] (f : K ⟶ L) (n : ℤ) :
    K.πTruncGE n ≫ truncGEMap f n = f ≫ L.πTruncGE n := by
  ext1
  simp

end Trunc

end CochainComplex.Plus

namespace CategoryTheory.Functor

section Comp

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {E : Type u₃} [Category.{v₃} E]

/-- Natural isomorphism `F.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus ≅
(F ⋙ G).mapCochainComplexPlus` for functors preserving zero morphisms. -/
def mapCochainComplexPlusCompIso [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroMorphisms E]
    (F : A ⥤ B) (G : B ⥤ E) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] :
    F.mapCochainComplexPlus ⋙ G.mapCochainComplexPlus ≅ (F ⋙ G).mapCochainComplexPlus :=
  NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _)) (fun _ ↦ by ext; simp)

@[simp]
lemma mapCochainComplexPlusCompIso_hom_app_hom [HasZeroMorphisms A] [HasZeroMorphisms B]
    [HasZeroMorphisms E] (F : A ⥤ B) (G : B ⥤ E) [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (K : CochainComplex.Plus A) :
    ((F.mapCochainComplexPlusCompIso G).hom.app K).hom = 𝟙 _ :=
  (rfl)

@[simp]
lemma mapCochainComplexPlusCompIso_inv_app_hom [HasZeroMorphisms A] [HasZeroMorphisms B]
    [HasZeroMorphisms E] (F : A ⥤ B) (G : B ⥤ E) [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (K : CochainComplex.Plus A) :
    ((F.mapCochainComplexPlusCompIso G).inv.app K).hom = 𝟙 _ :=
  (rfl)

instance [Preadditive A] [Preadditive B] [Preadditive E]
    (F : A ⥤ B) (G : B ⥤ E) [F.Additive] [G.Additive] :
    NatTrans.CommShift (F.mapCochainComplexPlusCompIso G).hom ℤ :=
  NatTrans.CommShift.of_comp_faithful (CochainComplex.Plus.ι E) (by
    have h : Functor.whiskerRight (F.mapCochainComplexPlusCompIso G).hom
          (CochainComplex.Plus.ι E) =
        (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft F.mapCochainComplexPlus G.mapCochainComplexPlusCompι.hom ≫
          (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight F.mapCochainComplexPlusCompι.hom (G.mapHomologicalComplex _) ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft (CochainComplex.Plus.ι A)
            (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom ≫
          (F ⋙ G).mapCochainComplexPlusCompι.inv := by
      ext K n
      simp [mapCochainComplexPlusCompIso]
    rw [h]
    infer_instance)

end Comp

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

/-- If `τ : F₁ ⟶ F₂` is a natural isomorphism between additive functors, then
`τ.mapCochainComplexPlus` is also an isomorphism. -/
instance isIso_mapCochainComplexPlus {A : Type u₁} [Category.{v₁} A] [Preadditive A]
    {B : Type u₂} [Category.{v₂} B] [Preadditive B]
    {F₁ F₂ : A ⥤ B} [F₁.Additive] [F₂.Additive] (τ : F₁ ⟶ F₂) [IsIso τ] :
    IsIso τ.mapCochainComplexPlus :=
  ⟨(inv τ).mapCochainComplexPlus,
    by rw [← mapCochainComplexPlus_comp, IsIso.hom_inv_id, mapCochainComplexPlus_id],
    by rw [← mapCochainComplexPlus_comp, IsIso.inv_hom_id, mapCochainComplexPlus_id]⟩

end CategoryTheory.NatTrans
