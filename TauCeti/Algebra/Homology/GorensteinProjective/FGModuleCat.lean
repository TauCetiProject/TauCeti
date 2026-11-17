/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.GorensteinProjective.Buchweitz
public import TauCeti.Algebra.Homology.GorensteinProjective.Frobenius
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Triangulated
public import TauCeti.Algebra.Homology.TotallyAcyclic.FGModuleCat
public import TauCeti.CategoryTheory.Exact.Stable.Functor.Equivalence
public import TauCeti.CategoryTheory.Triangulated.Equivalence

/-!
# Stable Gorenstein-projective modules as Gorenstein-projective objects of `mod-A`

Over a left noetherian ring `A`, `FGModuleCat.isGorensteinProjective_iff` identifies
`TauCeti.GorensteinProjectiveModuleCat A` with `CategoryTheory.GorensteinProjective (FGModuleCat A)`
via an exact equivalence `fgModuleCatEquivalence`, inducing a triangle equivalence
`stableFGModuleCatEquivalence` between their Happel-triangulated projective stable categories.
Composing with `CategoryTheory.GorensteinProjective.toSingularityCategory (FGModuleCat A)` yields
Chen's fully faithful triangle functor `toSingularityCategory` to `D_sg(mod-A)` and Buchweitz's
triangle equivalence `singularityEquivalence` over an Iwanaga–Gorenstein ring `A`.

## References

* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, AMS (2021), Theorem 4.4.1.
* Xiao-Wu Chen, *Relative singularity categories and Gorenstein-projective modules*, Math. Nachr.
  **284** (2011), 199–212.
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional Algebras*,
  Chapter I, Section 2.
-/

public section

noncomputable section

open CategoryTheory Limits Pretriangulated

universe w v u

namespace TauCeti.GorensteinProjectiveModuleCat

section Noetherian

variable (A : Type u) [Ring A] [IsNoetherianRing A] [Small.{v} A]

/-- View a finitely generated Gorenstein-projective `A`-module in
`GorensteinProjective (FGModuleCat A)`. -/
def toFGModuleCat : GorensteinProjectiveModuleCat.{v} A ⥤ GorensteinProjective (FGModuleCat.{v} A)
    where
  obj X := ⟨⟨X.obj, (ModuleCat.isFG_iff _).2 X.property.finite⟩,
    (FGModuleCat.isGorensteinProjective_iff _).2 X.property⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk f.hom)

variable {A} in
@[simp] theorem toFGModuleCat_obj_obj (X : GorensteinProjectiveModuleCat.{v} A) :
    ((toFGModuleCat A).obj X).obj = ⟨X.obj, (ModuleCat.isFG_iff _).2 X.property.finite⟩ := (rfl)

/-- Composing `toFGModuleCat` with forgetful inclusions recovers `(IsGorensteinProjective A).ι`. -/
theorem toFGModuleCat_comp_ι_comp_forget₂ :
    toFGModuleCat.{v} A ⋙ (isGorensteinProjective (FGModuleCat.{v} A)).ι ⋙
        forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) = (IsGorensteinProjective A).ι := (rfl)

variable {A} in
theorem toFGModuleCat_map_hom_hom {X Y : GorensteinProjectiveModuleCat.{v} A} (f : X ⟶ Y) :
    ((toFGModuleCat A).map f).hom.hom =
      eqToHom (congrArg ObjectProperty.FullSubcategory.obj (toFGModuleCat_obj_obj X)) ≫ f.hom ≫
        eqToHom (congrArg ObjectProperty.FullSubcategory.obj (toFGModuleCat_obj_obj Y)).symm := by
  -- `forget₂` is `(ModuleCat.isFG A).ι` by `ObjectProperty.FullSubcategory.hasForget₂`.
  have h := toFGModuleCat_comp_ι_comp_forget₂.{v} A
  rw [show forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) = (ModuleCat.isFG A).ι from rfl] at h
  simpa only [Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map]
    using Functor.congr_hom h f

variable {A} in
@[simp] theorem toFGModuleCat_map_hom {X Y : GorensteinProjectiveModuleCat.{v} A} (f : X ⟶ Y) :
    ((toFGModuleCat A).map f).hom =
      eqToHom (toFGModuleCat_obj_obj X) ≫ ObjectProperty.homMk f.hom ≫
        eqToHom (toFGModuleCat_obj_obj Y).symm := by
  apply ObjectProperty.hom_ext
  rw [toFGModuleCat_map_hom_hom f, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
  simp only [← (ModuleCat.isFG A).ι_map, eqToHom_map]

instance : (toFGModuleCat.{v} A).Additive where

/-- View a Gorenstein-projective object of `FGModuleCat A` in `GorensteinProjectiveModuleCat A`. -/
def fromFGModuleCat :
    GorensteinProjective (FGModuleCat.{v} A) ⥤ GorensteinProjectiveModuleCat.{v} A where
  obj Y := ⟨Y.obj.obj, (FGModuleCat.isGorensteinProjective_iff Y.obj).1 Y.property⟩
  map g := ObjectProperty.homMk g.hom.hom

variable {A} in
@[simp] theorem fromFGModuleCat_obj_obj (Y : GorensteinProjective (FGModuleCat.{v} A)) :
    ((fromFGModuleCat A).obj Y).obj = Y.obj.obj := (rfl)

/-- Composing `fromFGModuleCat` with `(IsGorensteinProjective A).ι` forgets both predicates. -/
theorem fromFGModuleCat_comp_ι :
    fromFGModuleCat.{v} A ⋙ (IsGorensteinProjective A).ι =
      (isGorensteinProjective (FGModuleCat.{v} A)).ι ⋙
        forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) := (rfl)

variable {A} in
@[simp] theorem fromFGModuleCat_map_hom {X Y : GorensteinProjective (FGModuleCat.{v} A)}
    (g : X ⟶ Y) : ((fromFGModuleCat A).map g).hom =
      eqToHom (fromFGModuleCat_obj_obj X) ≫ g.hom.hom ≫
        eqToHom (fromFGModuleCat_obj_obj Y).symm := by
  -- `forget₂` is `(ModuleCat.isFG A).ι` by `ObjectProperty.FullSubcategory.hasForget₂`.
  have h := fromFGModuleCat_comp_ι.{v} A
  rw [show forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) = (ModuleCat.isFG A).ι from rfl] at h
  simpa only [Functor.comp_obj, Functor.comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map]
    using Functor.congr_hom h g

@[simp] theorem toFGModuleCat_comp_fromFGModuleCat :
    toFGModuleCat.{v} A ⋙ fromFGModuleCat.{v} A = 𝟭 _ := (rfl)
@[simp] theorem fromFGModuleCat_comp_toFGModuleCat :
    fromFGModuleCat.{v} A ⋙ toFGModuleCat.{v} A = 𝟭 _ := (rfl)

instance : (fromFGModuleCat.{v} A).Additive where

/-- Equivalence between `GorensteinProjectiveModuleCat A` and
`GorensteinProjective (FGModuleCat A)` over a left noetherian ring `A`. -/
def fgModuleCatEquivalence :
    GorensteinProjectiveModuleCat.{v} A ≌ GorensteinProjective (FGModuleCat.{v} A) where
  functor := toFGModuleCat A
  inverse := fromFGModuleCat A
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp] theorem fgModuleCatEquivalence_functor :
    (fgModuleCatEquivalence.{v} A).functor = toFGModuleCat A := (rfl)
@[simp] theorem fgModuleCatEquivalence_inverse :
    (fgModuleCatEquivalence.{v} A).inverse = fromFGModuleCat A := (rfl)
@[simp] theorem fgModuleCatEquivalence_unitIso :
    (fgModuleCatEquivalence.{v} A).unitIso = eqToIso (by simp) := (rfl)
@[simp] theorem fgModuleCatEquivalence_counitIso :
    (fgModuleCatEquivalence.{v} A).counitIso = eqToIso (by simp) := (rfl)

instance : (fgModuleCatEquivalence.{v} A).functor.Additive := by
  rw [fgModuleCatEquivalence_functor]; infer_instance
instance : (fgModuleCatEquivalence.{v} A).inverse.Additive := by
  rw [fgModuleCatEquivalence_inverse]; infer_instance

/-- `toFGModuleCat` preserves conflations. -/
theorem isConflationExact_toFGModuleCat :
    (exactStructure.{v} A).IsConflationExact
      (GorensteinProjective.exactStructure (FGModuleCat.{v} A)) (toFGModuleCat A) where
  map_conflation {S} hS := by
    simp only [exactStructure_conflation_iff, ← toFGModuleCat_comp_ι_comp_forget₂, ← Functor.assoc,
      ShortComplex.map_comp] at hS
    rw [GorensteinProjective.exactStructure_conflation_iff]
    let F := forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)
    let S' := (S.map (toFGModuleCat A)).map (isGorensteinProjective (FGModuleCat.{v} A)).ι
    exact { exact := (S'.exact_map_iff_of_faithful F).1 hS.exact
            mono_f := F.mono_of_mono_map hS.mono_f, epi_g := F.epi_of_epi_map hS.epi_g }

/-- `fromFGModuleCat` preserves conflations. -/
theorem isConflationExact_fromFGModuleCat :
    (GorensteinProjective.exactStructure (FGModuleCat.{v} A)).IsConflationExact
      (exactStructure.{v} A) (fromFGModuleCat A) where
  map_conflation {S} hS := by
    rw [GorensteinProjective.exactStructure_conflation_iff] at hS
    simp only [exactStructure_conflation_iff, ← ShortComplex.map_comp, fromFGModuleCat_comp_ι]
    rw [ShortComplex.map_comp]
    exact hS.map_of_exact (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A))

/-- `toFGModuleCat` preserves conflations and projective-injectives. -/
theorem stableConflationExact_toFGModuleCat :
    StableConflationExact (exactStructure.{v} A)
      (GorensteinProjective.exactStructure (FGModuleCat.{v} A)) (toFGModuleCat A) :=
  ExactStructure.IsConflationExact.stableConflationExact_of_equivalence
    (e := fgModuleCatEquivalence A) (isConflationExact_toFGModuleCat A)
    (isConflationExact_fromFGModuleCat A)
/-- `fromFGModuleCat` preserves conflations and projective-injectives. -/
theorem stableConflationExact_fromFGModuleCat :
    StableConflationExact (GorensteinProjective.exactStructure (FGModuleCat.{v} A))
      (exactStructure.{v} A) (fromFGModuleCat A) := by
  have : (fgModuleCatEquivalence A).symm.functor.Additive := by
    rw [Equivalence.symm_functor, fgModuleCatEquivalence_inverse]; infer_instance
  exact ExactStructure.IsConflationExact.stableConflationExact_of_equivalence
    (e := (fgModuleCatEquivalence A).symm) (isConflationExact_fromFGModuleCat A)
    (isConflationExact_toFGModuleCat A)

/-- Projective stable equivalence between `GorensteinProjectiveModuleCat A` and
`GorensteinProjective (FGModuleCat A)`. -/
def stableFGModuleCatEquivalence :
    (exactStructure.{v} A).ProjectiveStableCategory ≌
      (GorensteinProjective.exactStructure (FGModuleCat.{v} A)).ProjectiveStableCategory :=
  StableConflationExact.stableEquivalence (fgModuleCatEquivalence A)
    (stableConflationExact_toFGModuleCat A) (stableConflationExact_fromFGModuleCat A)
    exactStructure_isFrobenius GorensteinProjective.exactStructure_isFrobenius

theorem stableFGModuleCatEquivalence_functor :
    (stableFGModuleCatEquivalence A).functor =
      (stableConflationExact_toFGModuleCat A).stableFunctor exactStructure_isFrobenius :=
  StableConflationExact.stableEquivalence_functor _ _ _ _ _
theorem stableFGModuleCatEquivalence_inverse :
    (stableFGModuleCatEquivalence A).inverse =
      (stableConflationExact_fromFGModuleCat A).stableFunctor
        GorensteinProjective.exactStructure_isFrobenius :=
  StableConflationExact.stableEquivalence_inverse _ _ _ _ _

instance : (stableFGModuleCatEquivalence A).functor.Additive := by
  rw [stableFGModuleCatEquivalence_functor, StableConflationExact.stableFunctor_eq_map]
  infer_instance
instance : (stableFGModuleCatEquivalence A).inverse.Additive := by
  rw [stableFGModuleCatEquivalence_inverse, StableConflationExact.stableFunctor_eq_map]
  infer_instance

/-- `(stableFGModuleCatEquivalence A).functor` intertwines the stable quotient functors. -/
theorem projectiveStableFunctor_comp_stableFGModuleCatEquivalence_functor :
    (exactStructure.{v} A).projectiveStableFunctor ⋙ (stableFGModuleCatEquivalence A).functor =
      toFGModuleCat A ⋙
        (GorensteinProjective.exactStructure (FGModuleCat.{v} A)).projectiveStableFunctor := by
  rw [stableFGModuleCatEquivalence_functor, StableConflationExact.stableFunctor_eq_map,
    MorphismIdeal.quotientFunctor_comp_map]
/-- `(stableFGModuleCatEquivalence A).inverse` intertwines the stable quotient functors. -/
theorem projectiveStableFunctor_comp_stableFGModuleCatEquivalence_inverse :
    (GorensteinProjective.exactStructure (FGModuleCat.{v} A)).projectiveStableFunctor ⋙
        (stableFGModuleCatEquivalence A).inverse =
      fromFGModuleCat A ⋙ (exactStructure.{v} A).projectiveStableFunctor := by
  rw [stableFGModuleCatEquivalence_inverse, StableConflationExact.stableFunctor_eq_map,
    MorphismIdeal.quotientFunctor_comp_map]

section
variable {A}
@[simp] theorem stableFGModuleCatEquivalence_functor_obj_projectiveStableFunctor_obj
    (X : GorensteinProjectiveModuleCat.{v} A) :
    (stableFGModuleCatEquivalence A).functor.obj
        ((exactStructure A).projectiveStableFunctor.obj X) =
      (GorensteinProjective.exactStructure (FGModuleCat.{v} A)).projectiveStableFunctor.obj
        ((toFGModuleCat A).obj X) :=
  Functor.congr_obj (projectiveStableFunctor_comp_stableFGModuleCatEquivalence_functor A) X
@[simp] theorem stableFGModuleCatEquivalence_functor_map_projectiveStableFunctor_map
    {X Y : GorensteinProjectiveModuleCat.{v} A} (f : X ⟶ Y) :
    (stableFGModuleCatEquivalence A).functor.map
        ((exactStructure A).projectiveStableFunctor.map f) =
      eqToHom (stableFGModuleCatEquivalence_functor_obj_projectiveStableFunctor_obj X) ≫
        (GorensteinProjective.exactStructure (FGModuleCat.{v} A)).projectiveStableFunctor.map
          ((toFGModuleCat A).map f) ≫
        eqToHom (stableFGModuleCatEquivalence_functor_obj_projectiveStableFunctor_obj Y).symm :=
  Functor.congr_hom (projectiveStableFunctor_comp_stableFGModuleCatEquivalence_functor A) f
@[simp] theorem stableFGModuleCatEquivalence_inverse_obj_projectiveStableFunctor_obj
    (Y : GorensteinProjective (FGModuleCat.{v} A)) :
    (stableFGModuleCatEquivalence A).inverse.obj
        ((GorensteinProjective.exactStructure (FGModuleCat.{v} A)).projectiveStableFunctor.obj Y) =
      (exactStructure A).projectiveStableFunctor.obj ((fromFGModuleCat A).obj Y) :=
  Functor.congr_obj (projectiveStableFunctor_comp_stableFGModuleCatEquivalence_inverse A) Y
@[simp] theorem stableFGModuleCatEquivalence_inverse_map_projectiveStableFunctor_map
    {X Y : GorensteinProjective (FGModuleCat.{v} A)} (g : X ⟶ Y) :
    (stableFGModuleCatEquivalence A).inverse.map
        ((GorensteinProjective.exactStructure (FGModuleCat.{v} A)).projectiveStableFunctor.map g) =
      eqToHom (stableFGModuleCatEquivalence_inverse_obj_projectiveStableFunctor_obj X) ≫
        (exactStructure A).projectiveStableFunctor.map ((fromFGModuleCat A).map g) ≫
        eqToHom (stableFGModuleCatEquivalence_inverse_obj_projectiveStableFunctor_obj Y).symm :=
  Functor.congr_hom (projectiveStableFunctor_comp_stableFGModuleCatEquivalence_inverse A) g
end

/-- Shift compatibility for `(stableFGModuleCatEquivalence A).functor`. -/
@[instance_reducible] def stableFGModuleCatEquivalenceFunctorCommShift :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (GorensteinProjective.exactStructure_isFrobenius (C := FGModuleCat A)).stableHasShift
    (stableFGModuleCatEquivalence A).functor.CommShift ℤ :=
  StableConflationExact.stableEquivalenceFunctorCommShift (e := fgModuleCatEquivalence A)
    (stableConflationExact_toFGModuleCat A) (stableConflationExact_fromFGModuleCat A) _ _

/-- Shift comparison of `(stableFGModuleCatEquivalence A).functor` via `toFGModuleCat`. -/
theorem stableFGModuleCatEquivalenceFunctor_commShiftIso (n : ℤ) :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (GorensteinProjective.exactStructure_isFrobenius (C := FGModuleCat A)).stableHasShift
    letI := (stableConflationExact_toFGModuleCat A).stableFunctorCommShift
      exactStructure_isFrobenius GorensteinProjective.exactStructure_isFrobenius
    letI := stableFGModuleCatEquivalenceFunctorCommShift A
    (stableFGModuleCatEquivalence A).functor.commShiftIso n =
      Functor.isoWhiskerLeft (shiftFunctor (exactStructure.{v} A).ProjectiveStableCategory n)
        (eqToIso (stableFGModuleCatEquivalence_functor A)) ≪≫
      ((stableConflationExact_toFGModuleCat A).stableFunctor
        exactStructure_isFrobenius).commShiftIso n ≪≫
      Functor.isoWhiskerRight (eqToIso (stableFGModuleCatEquivalence_functor A)).symm
        (shiftFunctor
          (GorensteinProjective.exactStructure (FGModuleCat.{v} A)).ProjectiveStableCategory n) :=
  StableConflationExact.stableEquivalenceFunctor_commShiftIso (e := fgModuleCatEquivalence A)
    (stableConflationExact_toFGModuleCat A) (stableConflationExact_fromFGModuleCat A) _ _ n

/-- Shift compatibility for `(stableFGModuleCatEquivalence A).inverse`. -/
@[instance_reducible] def stableFGModuleCatEquivalenceInverseCommShift :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (GorensteinProjective.exactStructure_isFrobenius (C := FGModuleCat A)).stableHasShift
    (stableFGModuleCatEquivalence A).inverse.CommShift ℤ :=
  StableConflationExact.stableEquivalenceInverseCommShift (e := fgModuleCatEquivalence A)
    (stableConflationExact_toFGModuleCat A) (stableConflationExact_fromFGModuleCat A) _ _

/-- Shift comparison of `(stableFGModuleCatEquivalence A).inverse` as `commShiftInverse`. -/
theorem stableFGModuleCatEquivalenceInverse_commShiftIso (n : ℤ) :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (GorensteinProjective.exactStructure_isFrobenius (C := FGModuleCat A)).stableHasShift
    letI := stableFGModuleCatEquivalenceFunctorCommShift A
    (letI := stableFGModuleCatEquivalenceInverseCommShift A;
      (stableFGModuleCatEquivalence A).inverse.commShiftIso n) =
      (letI := (stableFGModuleCatEquivalence A).commShiftInverse ℤ;
        (stableFGModuleCatEquivalence A).inverse.commShiftIso n) :=
  StableConflationExact.stableEquivalenceInverse_commShiftIso (e := fgModuleCatEquivalence A)
    (stableConflationExact_toFGModuleCat A) (stableConflationExact_fromFGModuleCat A) _ _ n

/-- `stableFGModuleCatEquivalence` is a triangle equivalence for Happel's triangulations. -/
theorem stableFGModuleCatEquivalence_isTriangulated :
    letI hE := exactStructure_isFrobenius (A := A)
    letI hE' := GorensteinProjective.exactStructure_isFrobenius (C := FGModuleCat.{v} A)
    letI := hE.stableHasShift; letI := hE'.stableHasShift
    letI := hE.stableShiftFunctor_additive; letI := hE'.stableShiftFunctor_additive
    letI := hE.stablePretriangulated; letI := hE'.stablePretriangulated
    letI := stableFGModuleCatEquivalenceFunctorCommShift A
    letI := stableFGModuleCatEquivalenceInverseCommShift A
    letI := (stableFGModuleCatEquivalence A).commShift_of_functor ℤ
    (stableFGModuleCatEquivalence A).IsTriangulated :=
  StableConflationExact.stableEquivalenceIsTriangulated (e := fgModuleCatEquivalence A)
    (stableConflationExact_toFGModuleCat A) (stableConflationExact_fromFGModuleCat A) _ _

section Singularity

variable [HasDerivedCategory.{w} (FGModuleCat.{v} A)]

/-- **Chen's functor** on `(exactStructure A).ProjectiveStableCategory`, placing a finitely
generated Gorenstein-projective `A`-module in degree zero of `D_sg(mod-A)`. -/
def toSingularityCategory :
    (exactStructure.{v} A).ProjectiveStableCategory ⥤ SingularityCategory (FGModuleCat.{v} A) :=
  (stableFGModuleCatEquivalence A).functor ⋙
    GorensteinProjective.toSingularityCategory (FGModuleCat.{v} A)

theorem toSingularityCategory_def :
    toSingularityCategory.{w, v} A =
      (stableFGModuleCatEquivalence A).functor ⋙
        GorensteinProjective.toSingularityCategory (FGModuleCat.{v} A) := (rfl)

instance : (toSingularityCategory.{w, v} A).Additive := by
  rw [toSingularityCategory_def]; infer_instance
instance : (toSingularityCategory.{w, v} A).Full := by
  rw [toSingularityCategory_def]; infer_instance
instance : (toSingularityCategory.{w, v} A).Faithful := by
  rw [toSingularityCategory_def]; infer_instance

/-- **Chen's theorem**: `toSingularityCategory` is fully faithful over any left noetherian ring. -/
def fullyFaithfulToSingularityCategory : (toSingularityCategory.{w, v} A).FullyFaithful :=
  .ofFullyFaithful _

/-- `toSingularityCategory` restricts along `projectiveStableFunctor` to degree-zero placement. -/
theorem projectiveStableFunctor_comp_toSingularityCategory :
    (exactStructure.{v} A).projectiveStableFunctor ⋙ toSingularityCategory.{w, v} A =
      toFGModuleCat A ⋙ GorensteinProjective.toSingularityCategoryFunctor (FGModuleCat.{v} A) := by
  rw [toSingularityCategory_def, ← Functor.assoc,
    projectiveStableFunctor_comp_stableFGModuleCatEquivalence_functor, Functor.assoc,
    GorensteinProjective.projectiveStableFunctor_comp_toSingularityCategory]

variable {A} in
@[simp] theorem toSingularityCategory_obj_projectiveStableFunctor_obj
    (X : GorensteinProjectiveModuleCat.{v} A) :
    (toSingularityCategory.{w, v} A).obj ((exactStructure A).projectiveStableFunctor.obj X) =
      (SingularityCategory.Q (FGModuleCat.{v} A)).obj
        ((DerivedCategory.Bounded.singleFunctor (FGModuleCat.{v} A) 0).obj
          ⟨X.obj, (ModuleCat.isFG_iff _).2 X.property.finite⟩) := by
  rw [toSingularityCategory_def, Functor.comp_obj,
    stableFGModuleCatEquivalence_functor_obj_projectiveStableFunctor_obj,
    GorensteinProjective.toSingularityCategory_obj_projectiveStableFunctor_obj,
    toFGModuleCat_obj_obj]

variable {A} in
@[simp] theorem toSingularityCategory_map_projectiveStableFunctor_map
    {X Y : GorensteinProjectiveModuleCat.{v} A} (f : X ⟶ Y) :
    (toSingularityCategory.{w, v} A).map ((exactStructure A).projectiveStableFunctor.map f) =
      eqToHom (toSingularityCategory_obj_projectiveStableFunctor_obj X) ≫
        (SingularityCategory.Q (FGModuleCat.{v} A)).map
          ((DerivedCategory.Bounded.singleFunctor (FGModuleCat.{v} A) 0).map
            (ObjectProperty.homMk f.hom :
              (⟨X.obj, (ModuleCat.isFG_iff _).2 X.property.finite⟩ : FGModuleCat.{v} A) ⟶ _)) ≫
        eqToHom (toSingularityCategory_obj_projectiveStableFunctor_obj Y).symm :=
  Functor.congr_hom (projectiveStableFunctor_comp_toSingularityCategory.{w, v} A) f

/-- Shift compatibility for `toSingularityCategory`. -/
@[instance_reducible] def toSingularityCategoryCommShift :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    (toSingularityCategory.{w, v} A).CommShift ℤ := by
  letI := (exactStructure_isFrobenius (A := A)).stableHasShift
  letI := (GorensteinProjective.exactStructure_isFrobenius (C := FGModuleCat A)).stableHasShift
  letI := stableFGModuleCatEquivalenceFunctorCommShift A
  letI := GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{v} A)
  exact Functor.CommShift.ofIso (eqToIso (toSingularityCategory_def.{w, v} A).symm) ℤ

/-- Shift comparison of `toSingularityCategory` as a composite shift comparison. -/
theorem toSingularityCategory_commShiftIso (n : ℤ) :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (GorensteinProjective.exactStructure_isFrobenius (C := FGModuleCat A)).stableHasShift
    letI := stableFGModuleCatEquivalenceFunctorCommShift A
    letI := GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{v} A)
    letI := toSingularityCategoryCommShift.{w, v} A
    (toSingularityCategory.{w, v} A).commShiftIso n =
      Functor.isoWhiskerLeft (shiftFunctor (exactStructure.{v} A).ProjectiveStableCategory n)
        (eqToIso (toSingularityCategory_def.{w, v} A)) ≪≫
      ((stableFGModuleCatEquivalence A).functor ⋙
        GorensteinProjective.toSingularityCategory (FGModuleCat.{v} A)).commShiftIso n ≪≫
      Functor.isoWhiskerRight (eqToIso (toSingularityCategory_def.{w, v} A)).symm
        (shiftFunctor (SingularityCategory (FGModuleCat.{v} A)) n) := (rfl)

/-- **Chen's functor on `GorensteinProjectiveModuleCat A` is a triangle functor.** -/
theorem toSingularityCategory_isTriangulated :
    letI hE := exactStructure_isFrobenius (A := A)
    letI := hE.stableHasShift; letI := hE.stableShiftFunctor_additive
    letI := hE.stablePretriangulated; letI := toSingularityCategoryCommShift.{w, v} A
    (toSingularityCategory.{w, v} A).IsTriangulated := by
  have hE := exactStructure_isFrobenius (A := A)
  have hE' := GorensteinProjective.exactStructure_isFrobenius (C := FGModuleCat.{v} A)
  let := hE.stableHasShift; let := hE'.stableHasShift
  let := hE.stableShiftFunctor_additive; let := hE'.stableShiftFunctor_additive
  let := hE.stablePretriangulated; let := hE'.stablePretriangulated
  let := stableFGModuleCatEquivalenceFunctorCommShift A
  let := stableFGModuleCatEquivalenceInverseCommShift A
  let := (stableFGModuleCatEquivalence A).commShift_of_functor ℤ
  have := stableFGModuleCatEquivalence_isTriangulated A
  let := GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{v} A)
  have := GorensteinProjective.toSingularityCategory_isTriangulated (C := FGModuleCat.{v} A)
  let := toSingularityCategoryCommShift.{w, v} A
  have := Functor.CommShift.ofIso_compatibility
    (eqToIso (toSingularityCategory_def.{w, v} A).symm) ℤ
  exact Functor.isTriangulated_of_iso (eqToIso (toSingularityCategory_def.{w, v} A).symm)

end Singularity

end Noetherian

section Buchweitz

variable (A : Type u) [Ring A] [IsIwanagaGorenstein A] [HasDerivedCategory.{w} (FGModuleCat.{u} A)]

/-- **Buchweitz's theorem**: over an Iwanaga–Gorenstein ring, `toSingularityCategory` is an
equivalence of categories. -/
instance isEquivalence_toSingularityCategory :
    (toSingularityCategory.{w, u} A).IsEquivalence := by
  rw [toSingularityCategory_def]; infer_instance

/-- **Buchweitz's equivalence** `(exactStructure A).ProjectiveStableCategory ≌ D_sg(mod-A)` over an
Iwanaga–Gorenstein ring `A`. -/
def singularityEquivalence :
    (exactStructure.{u} A).ProjectiveStableCategory ≌ SingularityCategory (FGModuleCat.{u} A) :=
  (toSingularityCategory.{w, u} A).asEquivalence

@[simp] theorem singularityEquivalence_functor :
    (singularityEquivalence.{w, u} A).functor = toSingularityCategory.{w, u} A := (rfl)

/-- **Buchweitz's equivalence is triangulated.** -/
theorem singularityEquivalence_isTriangulated :
    letI hE := exactStructure_isFrobenius (A := A)
    letI := hE.stableHasShift; letI := hE.stableShiftFunctor_additive
    letI := hE.stablePretriangulated; letI := toSingularityCategoryCommShift.{w, u} A
    letI : (singularityEquivalence.{w, u} A).functor.CommShift ℤ :=
      Functor.CommShift.ofIso (eqToIso (singularityEquivalence_functor.{w, u} A).symm) ℤ
    letI := (singularityEquivalence.{w, u} A).commShiftInverse ℤ
    letI := (singularityEquivalence.{w, u} A).commShift_of_functor ℤ
    (singularityEquivalence.{w, u} A).IsTriangulated := by
  have hE := exactStructure_isFrobenius (A := A)
  let := hE.stableHasShift; let := hE.stableShiftFunctor_additive; let := hE.stablePretriangulated
  let := toSingularityCategoryCommShift.{w, u} A
  have := toSingularityCategory_isTriangulated.{w, u} A
  exact (singularityEquivalence.{w, u} A).isTriangulated_of_functor_eq
    (singularityEquivalence_functor.{w, u} A)

end Buchweitz

end TauCeti.GorensteinProjectiveModuleCat
