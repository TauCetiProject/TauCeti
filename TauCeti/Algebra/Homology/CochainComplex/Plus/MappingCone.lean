/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# Mapping cones on `CochainComplex.Plus`

This file constructs mapping cones and mapping cone triangles in Mathlib's category
`CochainComplex.Plus C` of bounded-below `ℤ`-indexed cochain complexes:

* `CochainComplex.Plus.mappingCone`: the mapping cone of a morphism in `CochainComplex.Plus C`.
* `CochainComplex.Plus.mappingConeTriangle`: the mapping cone triangle `K ⟶ L ⟶ cone(f) ⟶ K⟦1⟧`
  in `CochainComplex.Plus C`, together with component formulas and the identification
  `CochainComplex.Plus.mappingConeTriangleιIso` with `CochainComplex.mappingCone.triangle f.hom`.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ u₁

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

-- Because `mappingConeTriangle` and `mappingCone` are intentionally not `@[expose]`, public lemma
-- statements cannot identify `(mappingConeTriangle f).objᵢ` or `(mappingCone f).obj`
-- definitionally and therefore conjugate morphisms by `eqToHom (mappingConeTriangle_objᵢ f)`.

/-- First morphism of `mappingConeTriangle f`. -/
@[simp]
lemma mappingConeTriangle_mor₁ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangle f).mor₁ =
      eqToHom (mappingConeTriangle_obj₁ f) ≫ f ≫
        eqToHom (mappingConeTriangle_obj₂ f).symm :=
  -- Definitional through `Triangle.mk` in `mappingConeTriangle`, transported across `eqToHom`.
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
  -- Definitional through `Triangle.mk` and `ObjectProperty.homMk` up to `eqToHom`.
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
  -- Definitional through `Triangle.mk` in `mappingConeTriangle`, transported across `eqToHom`.
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
  -- Definitional from `Triangle.isoMk` and `mappingConeTriangleιIso`.
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_hom_hom₂ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).hom.hom₂ =
      eqToHom (congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₂ f)) :=
  -- Definitional from `Triangle.isoMk` and `mappingConeTriangleιIso`.
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_hom_hom₃ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).hom.hom₃ =
      eqToHom ((congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₃ f)).trans
        (mappingCone_obj f)) :=
  -- Definitional from `Triangle.isoMk` and `mappingConeTriangleιIso`.
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_inv_hom₁ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).inv.hom₁ =
      eqToHom (congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₁ f)).symm :=
  -- Definitional from `Triangle.isoMk` and `mappingConeTriangleιIso`.
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_inv_hom₂ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).inv.hom₂ =
      eqToHom (congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₂ f)).symm :=
  -- Definitional from `Triangle.isoMk` and `mappingConeTriangleιIso`.
  (rfl)

@[simp]
lemma mappingConeTriangleιIso_inv_hom₃ {K L : CochainComplex.Plus C} (f : K ⟶ L) :
    (mappingConeTriangleιIso f).inv.hom₃ =
      eqToHom ((congrArg ObjectProperty.FullSubcategory.obj (mappingConeTriangle_obj₃ f)).trans
        (mappingCone_obj f)).symm :=
  -- Definitional from `Triangle.isoMk` and `mappingConeTriangleιIso`.
  (rfl)

end MappingCone

end CochainComplex.Plus
