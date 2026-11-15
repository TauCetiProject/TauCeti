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

Over a left noetherian ring `A`, finitely generated Gorenstein-projective `A`-modules appear in two
equivalent guises:

* `TauCeti.GorensteinProjectiveModuleCat A`, the full subcategory of `ModuleCat A` cut out by
  `TauCeti.IsGorensteinProjective A`, with the Frobenius exact structure inherited from
  `ModuleCat A` (`TauCeti.GorensteinProjectiveModuleCat.exactStructure_isFrobenius`);
* `CategoryTheory.GorensteinProjective (FGModuleCat A)`, the Gorenstein-projective objects of the
  abelian category `FGModuleCat A`, with the Frobenius exact structure inherited from
  `FGModuleCat A` (`CategoryTheory.GorensteinProjective.exactStructure_isFrobenius`).

By `FGModuleCat.isGorensteinProjective_iff`, the two underlying predicates agree on finitely
generated modules, and because `forget₂ (FGModuleCat A) (ModuleCat A)` preserves and reflects short
exact sequences, the resulting additive equivalence preserves conflations in both directions. It
therefore induces a triangle equivalence between their Happel-triangulated projective stable
categories (`TauCeti.GorensteinProjectiveModuleCat.stableFGModuleCatEquivalence`).

Composing this stable equivalence with Chen's fully faithful triangle functor
`CategoryTheory.GorensteinProjective.toSingularityCategory (FGModuleCat A)` transports Chen's
embedding and Buchweitz's equivalence directly to the module-level stable category
`(GorensteinProjectiveModuleCat.exactStructure A).ProjectiveStableCategory` used by matrix
factorization cokernels.

## Main definitions and results

In `TauCeti.GorensteinProjectiveModuleCat`:

* `fgModuleCatEquivalence`: the exact equivalence
  `GorensteinProjectiveModuleCat A ≌ CategoryTheory.GorensteinProjective (FGModuleCat A)`.
* `stableFGModuleCatEquivalence` and `stableFGModuleCatEquivalence_isTriangulated`: the induced
  triangle equivalence on projective stable categories.
* `toSingularityCategory` and `toSingularityCategory_isTriangulated`: Chen's fully faithful
  triangle functor `(exactStructure A).ProjectiveStableCategory ⥤ SingularityCategory`
  placing a Gorenstein-projective module in degree zero of `D_sg(mod-A)`.
* `isEquivalence_toSingularityCategory`, `singularityEquivalence`, and
  `singularityEquivalence_isTriangulated`: **Buchweitz's theorem** for
  `GorensteinProjectiveModuleCat A` over an Iwanaga–Gorenstein ring `A`.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Theorem 4.4.1.
* Xiao-Wu Chen, *Relative singularity categories and Gorenstein-projective modules*, Math. Nachr.
  **284** (2011), 199–212.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace TauCeti.GorensteinProjectiveModuleCat

section Noetherian

variable (A : Type u) [Ring A] [IsNoetherianRing A] [Small.{v} A]

/-- View a finitely generated Gorenstein-projective `A`-module as a Gorenstein-projective object of
`FGModuleCat A`. -/
def toFGModuleCat :
    GorensteinProjectiveModuleCat.{v} A ⥤
      CategoryTheory.GorensteinProjective (FGModuleCat.{v} A) where
  obj X := ⟨⟨X.obj, (ModuleCat.isFG_iff _).2 X.property.finite⟩,
    (FGModuleCat.isGorensteinProjective_iff _).2 X.property⟩
  map f := ObjectProperty.homMk (ObjectProperty.homMk f.hom)

variable {A} in
@[simp]
theorem toFGModuleCat_obj_obj (X : GorensteinProjectiveModuleCat.{v} A) :
    ((toFGModuleCat A).obj X).obj = ⟨X.obj, (ModuleCat.isFG_iff _).2 X.property.finite⟩ :=
  (rfl)

variable {A} in
/-- On morphisms, `toFGModuleCat` acts as the identity on underlying `ModuleCat A` morphisms. -/
@[simp]
theorem toFGModuleCat_map_hom {X Y : GorensteinProjectiveModuleCat.{v} A} (f : X ⟶ Y) :
    ((toFGModuleCat A).map f).hom =
      eqToHom (toFGModuleCat_obj_obj X) ≫
        ObjectProperty.homMk f.hom ≫
        eqToHom (toFGModuleCat_obj_obj Y).symm := by
  let f' : (⟨X.obj, (ModuleCat.isFG_iff _).2 X.property.finite⟩ : FGModuleCat.{v} A) ⟶
      ⟨Y.obj, (ModuleCat.isFG_iff _).2 Y.property.finite⟩ := ObjectProperty.homMk f.hom
  change f' = eqToHom rfl ≫ f' ≫ eqToHom rfl
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

variable {A} in
/-- Underlying `ModuleCat A` morphism of `(toFGModuleCat A).map f`. -/
theorem toFGModuleCat_map_hom_hom {X Y : GorensteinProjectiveModuleCat.{v} A} (f : X ⟶ Y) :
    ((toFGModuleCat A).map f).hom.hom =
      eqToHom (congrArg ObjectProperty.FullSubcategory.obj (toFGModuleCat_obj_obj X)) ≫
        f.hom ≫
        eqToHom (congrArg ObjectProperty.FullSubcategory.obj (toFGModuleCat_obj_obj Y)).symm := by
  change f.hom = eqToHom rfl ≫ f.hom ≫ eqToHom rfl
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Composing `toFGModuleCat` with the two forgetful inclusions into `ModuleCat A` recovers the
canonical inclusion `(IsGorensteinProjective A).ι`. -/
theorem toFGModuleCat_comp_ι_comp_forget₂ :
    toFGModuleCat.{v} A ⋙
        (CategoryTheory.isGorensteinProjective (FGModuleCat.{v} A)).ι ⋙
        forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) =
      (IsGorensteinProjective A).ι :=
  (rfl)

instance : (toFGModuleCat.{v} A).Additive where

/-- View a Gorenstein-projective object of `FGModuleCat A` as a finitely generated
Gorenstein-projective `A`-module. -/
def fromFGModuleCat :
    CategoryTheory.GorensteinProjective (FGModuleCat.{v} A) ⥤
      GorensteinProjectiveModuleCat.{v} A where
  obj Y := ⟨Y.obj.obj, (FGModuleCat.isGorensteinProjective_iff Y.obj).1 Y.property⟩
  map g := ObjectProperty.homMk g.hom.hom

variable {A} in
@[simp]
theorem fromFGModuleCat_obj_obj
    (Y : CategoryTheory.GorensteinProjective (FGModuleCat.{v} A)) :
    ((fromFGModuleCat A).obj Y).obj = Y.obj.obj :=
  (rfl)

variable {A} in
/-- On morphisms, `fromFGModuleCat` forgets Gorenstein projectivity and finite generation. -/
@[simp]
theorem fromFGModuleCat_map_hom
    {X Y : CategoryTheory.GorensteinProjective (FGModuleCat.{v} A)} (g : X ⟶ Y) :
    ((fromFGModuleCat A).map g).hom =
      eqToHom (fromFGModuleCat_obj_obj X) ≫ g.hom.hom ≫
        eqToHom (fromFGModuleCat_obj_obj Y).symm := by
  change g.hom.hom = eqToHom rfl ≫ g.hom.hom ≫ eqToHom rfl
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Composing `fromFGModuleCat` with `(IsGorensteinProjective A).ι` forgets Gorenstein projectivity
and finite generation. -/
theorem fromFGModuleCat_comp_ι :
    fromFGModuleCat.{v} A ⋙ (IsGorensteinProjective A).ι =
      (CategoryTheory.isGorensteinProjective (FGModuleCat.{v} A)).ι ⋙
        forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) :=
  (rfl)

@[simp]
theorem toFGModuleCat_comp_fromFGModuleCat :
    toFGModuleCat.{v} A ⋙ fromFGModuleCat.{v} A = 𝟭 _ :=
  (rfl)

@[simp]
theorem fromFGModuleCat_comp_toFGModuleCat :
    fromFGModuleCat.{v} A ⋙ toFGModuleCat.{v} A = 𝟭 _ :=
  (rfl)

instance : (fromFGModuleCat.{v} A).Additive where

/-- Over a left noetherian ring `A`, `GorensteinProjectiveModuleCat A` is equivalent to the
Gorenstein-projective objects of `FGModuleCat A`. -/
def fgModuleCatEquivalence :
    GorensteinProjectiveModuleCat.{v} A ≌
      CategoryTheory.GorensteinProjective (FGModuleCat.{v} A) where
  functor := toFGModuleCat A
  inverse := fromFGModuleCat A
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp]
theorem fgModuleCatEquivalence_functor :
    (fgModuleCatEquivalence.{v} A).functor = toFGModuleCat A :=
  (rfl)

@[simp]
theorem fgModuleCatEquivalence_inverse :
    (fgModuleCatEquivalence.{v} A).inverse = fromFGModuleCat A :=
  (rfl)

@[simp]
theorem fgModuleCatEquivalence_unitIso :
    (fgModuleCatEquivalence.{v} A).unitIso =
      eqToIso (by rw [fgModuleCatEquivalence_functor, fgModuleCatEquivalence_inverse,
        toFGModuleCat_comp_fromFGModuleCat]) :=
  (rfl)

@[simp]
theorem fgModuleCatEquivalence_counitIso :
    (fgModuleCatEquivalence.{v} A).counitIso =
      eqToIso (by rw [fgModuleCatEquivalence_inverse, fgModuleCatEquivalence_functor,
        fromFGModuleCat_comp_toFGModuleCat]) :=
  (rfl)

instance : (fgModuleCatEquivalence.{v} A).functor.Additive := by
  rw [fgModuleCatEquivalence_functor]
  infer_instance

instance : (fgModuleCatEquivalence.{v} A).inverse.Additive := by
  rw [fgModuleCatEquivalence_inverse]
  infer_instance

/-- `toFGModuleCat` preserves conflations. -/
theorem isConflationExact_toFGModuleCat :
    (exactStructure.{v} A).IsConflationExact
      (CategoryTheory.GorensteinProjective.exactStructure (FGModuleCat.{v} A))
      (toFGModuleCat A) where
  map_conflation {S} hS := by
    simp only [exactStructure_conflation_iff, ← toFGModuleCat_comp_ι_comp_forget₂, ← Functor.assoc,
      ShortComplex.map_comp] at hS
    rw [CategoryTheory.GorensteinProjective.exactStructure_conflation_iff]
    let F := forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)
    let S' := (S.map (toFGModuleCat A)).map
      (CategoryTheory.isGorensteinProjective (FGModuleCat.{v} A)).ι
    exact
      { exact := (S'.exact_map_iff_of_faithful F).1 hS.exact
        mono_f := F.mono_of_mono_map hS.mono_f
        epi_g := F.epi_of_epi_map hS.epi_g }

/-- `fromFGModuleCat` preserves conflations. -/
theorem isConflationExact_fromFGModuleCat :
    (CategoryTheory.GorensteinProjective.exactStructure (FGModuleCat.{v} A)).IsConflationExact
      (exactStructure.{v} A) (fromFGModuleCat A) where
  map_conflation {S} hS := by
    rw [CategoryTheory.GorensteinProjective.exactStructure_conflation_iff] at hS
    simp only [exactStructure_conflation_iff, ← ShortComplex.map_comp, fromFGModuleCat_comp_ι]
    rw [ShortComplex.map_comp]
    exact hS.map_of_exact (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A))

/-- `toFGModuleCat` preserves conflations and projective-injectives. -/
theorem stableConflationExact_toFGModuleCat :
    StableConflationExact (exactStructure.{v} A)
      (CategoryTheory.GorensteinProjective.exactStructure (FGModuleCat.{v} A))
      (toFGModuleCat A) :=
  ExactStructure.IsConflationExact.stableConflationExact_of_equivalence
    (e := fgModuleCatEquivalence A) (isConflationExact_toFGModuleCat A)
    (isConflationExact_fromFGModuleCat A)

/-- `fromFGModuleCat` preserves conflations and projective-injectives. -/
theorem stableConflationExact_fromFGModuleCat :
    StableConflationExact
      (CategoryTheory.GorensteinProjective.exactStructure (FGModuleCat.{v} A))
      (exactStructure.{v} A) (fromFGModuleCat A) := by
  have : (fgModuleCatEquivalence A).symm.functor.Additive := by
    rw [Equivalence.symm_functor, fgModuleCatEquivalence_inverse]
    infer_instance
  exact ExactStructure.IsConflationExact.stableConflationExact_of_equivalence
    (e := (fgModuleCatEquivalence A).symm) (isConflationExact_fromFGModuleCat A)
    (isConflationExact_toFGModuleCat A)

/-- The projective stable equivalence between `GorensteinProjectiveModuleCat A` and
`CategoryTheory.GorensteinProjective (FGModuleCat A)`. -/
def stableFGModuleCatEquivalence :
    (exactStructure.{v} A).ProjectiveStableCategory ≌
      (CategoryTheory.GorensteinProjective.exactStructure
        (FGModuleCat.{v} A)).ProjectiveStableCategory :=
  StableConflationExact.stableEquivalence (fgModuleCatEquivalence A)
    (stableConflationExact_toFGModuleCat A) (stableConflationExact_fromFGModuleCat A)
    exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius

/-- The forward functor of `stableFGModuleCatEquivalence` is the stable functor induced by
`toFGModuleCat`. -/
theorem stableFGModuleCatEquivalence_functor :
    (stableFGModuleCatEquivalence A).functor =
      (stableConflationExact_toFGModuleCat A).stableFunctor exactStructure_isFrobenius :=
  StableConflationExact.stableEquivalence_functor _ _ _ _ _

/-- The inverse functor of `stableFGModuleCatEquivalence` is the stable functor induced by
`fromFGModuleCat`. -/
theorem stableFGModuleCatEquivalence_inverse :
    (stableFGModuleCatEquivalence A).inverse =
      (stableConflationExact_fromFGModuleCat A).stableFunctor
        CategoryTheory.GorensteinProjective.exactStructure_isFrobenius :=
  StableConflationExact.stableEquivalence_inverse _ _ _ _ _

instance : (stableFGModuleCatEquivalence A).functor.Additive := by
  rw [stableFGModuleCatEquivalence_functor, StableConflationExact.stableFunctor_eq_map]
  infer_instance

instance : (stableFGModuleCatEquivalence A).inverse.Additive := by
  rw [stableFGModuleCatEquivalence_inverse, StableConflationExact.stableFunctor_eq_map]
  infer_instance

/-- On `GorensteinProjectiveModuleCat A`, `stableFGModuleCatEquivalence` intertwines the projective
stable quotient functors with `toFGModuleCat`. -/
theorem projectiveStableFunctor_comp_stableFGModuleCatEquivalence_functor :
    (exactStructure.{v} A).projectiveStableFunctor ⋙ (stableFGModuleCatEquivalence A).functor =
      toFGModuleCat A ⋙
        (CategoryTheory.GorensteinProjective.exactStructure
          (FGModuleCat.{v} A)).projectiveStableFunctor := by
  rw [stableFGModuleCatEquivalence_functor, StableConflationExact.stableFunctor_eq_map,
    MorphismIdeal.quotientFunctor_comp_map]

variable {A} in
/-- On objects from `GorensteinProjectiveModuleCat A`, `stableFGModuleCatEquivalence` applies
`toFGModuleCat`. -/
@[simp]
theorem stableFGModuleCatEquivalence_functor_obj_projectiveStableFunctor_obj
    (X : GorensteinProjectiveModuleCat.{v} A) :
    (stableFGModuleCatEquivalence A).functor.obj
        ((exactStructure A).projectiveStableFunctor.obj X) =
      (CategoryTheory.GorensteinProjective.exactStructure
        (FGModuleCat.{v} A)).projectiveStableFunctor.obj ((toFGModuleCat A).obj X) :=
  Functor.congr_obj (projectiveStableFunctor_comp_stableFGModuleCatEquivalence_functor A) X

variable {A} in
/-- On morphisms from `GorensteinProjectiveModuleCat A`, `stableFGModuleCatEquivalence` applies
`toFGModuleCat`. -/
@[simp]
theorem stableFGModuleCatEquivalence_functor_map_projectiveStableFunctor_map
    {X Y : GorensteinProjectiveModuleCat.{v} A} (f : X ⟶ Y) :
    (stableFGModuleCatEquivalence A).functor.map
        ((exactStructure A).projectiveStableFunctor.map f) =
      eqToHom (stableFGModuleCatEquivalence_functor_obj_projectiveStableFunctor_obj X) ≫
        (CategoryTheory.GorensteinProjective.exactStructure
          (FGModuleCat.{v} A)).projectiveStableFunctor.map ((toFGModuleCat A).map f) ≫
        eqToHom (stableFGModuleCatEquivalence_functor_obj_projectiveStableFunctor_obj Y).symm :=
  Functor.congr_hom (projectiveStableFunctor_comp_stableFGModuleCatEquivalence_functor A) f

/-- On `CategoryTheory.GorensteinProjective (FGModuleCat A)`, the inverse of
`stableFGModuleCatEquivalence` intertwines the projective stable quotient functors with
`fromFGModuleCat`. -/
theorem projectiveStableFunctor_comp_stableFGModuleCatEquivalence_inverse :
    (CategoryTheory.GorensteinProjective.exactStructure
        (FGModuleCat.{v} A)).projectiveStableFunctor ⋙
        (stableFGModuleCatEquivalence A).inverse =
      fromFGModuleCat A ⋙ (exactStructure.{v} A).projectiveStableFunctor := by
  rw [stableFGModuleCatEquivalence_inverse, StableConflationExact.stableFunctor_eq_map,
    MorphismIdeal.quotientFunctor_comp_map]

variable {A} in
/-- On objects from `CategoryTheory.GorensteinProjective (FGModuleCat A)`, the inverse of
`stableFGModuleCatEquivalence` applies `fromFGModuleCat`. -/
@[simp]
theorem stableFGModuleCatEquivalence_inverse_obj_projectiveStableFunctor_obj
    (Y : CategoryTheory.GorensteinProjective (FGModuleCat.{v} A)) :
    (stableFGModuleCatEquivalence A).inverse.obj
        ((CategoryTheory.GorensteinProjective.exactStructure
          (FGModuleCat.{v} A)).projectiveStableFunctor.obj Y) =
      (exactStructure A).projectiveStableFunctor.obj ((fromFGModuleCat A).obj Y) :=
  Functor.congr_obj (projectiveStableFunctor_comp_stableFGModuleCatEquivalence_inverse A) Y

variable {A} in
/-- On morphisms from `CategoryTheory.GorensteinProjective (FGModuleCat A)`, the inverse of
`stableFGModuleCatEquivalence` applies `fromFGModuleCat`. -/
@[simp]
theorem stableFGModuleCatEquivalence_inverse_map_projectiveStableFunctor_map
    {X Y : CategoryTheory.GorensteinProjective (FGModuleCat.{v} A)} (g : X ⟶ Y) :
    (stableFGModuleCatEquivalence A).inverse.map
        ((CategoryTheory.GorensteinProjective.exactStructure
          (FGModuleCat.{v} A)).projectiveStableFunctor.map g) =
      eqToHom (stableFGModuleCatEquivalence_inverse_obj_projectiveStableFunctor_obj X) ≫
        (exactStructure A).projectiveStableFunctor.map ((fromFGModuleCat A).map g) ≫
        eqToHom (stableFGModuleCatEquivalence_inverse_obj_projectiveStableFunctor_obj Y).symm :=
  Functor.congr_hom (projectiveStableFunctor_comp_stableFGModuleCatEquivalence_inverse A) g

/-- Shift compatibility for the forward functor of `stableFGModuleCatEquivalence`. -/
@[instance_reducible]
def stableFGModuleCatEquivalenceFunctorCommShift :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableHasShift
    (stableFGModuleCatEquivalence A).functor.CommShift ℤ := by
  letI := (exactStructure_isFrobenius (A := A)).stableHasShift
  letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
    (C := FGModuleCat.{v} A)).stableHasShift
  letI := (stableConflationExact_toFGModuleCat A).stableFunctorCommShift
    exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
  exact Functor.CommShift.ofIso (eqToIso (stableFGModuleCatEquivalence_functor A).symm) ℤ

/-- The shift comparison of `(stableFGModuleCatEquivalence A).functor` is the descended shift
comparison of `toFGModuleCat` transported along `stableFGModuleCatEquivalence_functor`. -/
theorem stableFGModuleCatEquivalenceFunctor_commShiftIso (n : ℤ) :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableHasShift
    letI := (stableConflationExact_toFGModuleCat A).stableFunctorCommShift
      exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
    letI := stableFGModuleCatEquivalenceFunctorCommShift A
    (stableFGModuleCatEquivalence A).functor.commShiftIso n =
      Functor.isoWhiskerLeft (shiftFunctor (exactStructure.{v} A).ProjectiveStableCategory n)
        (eqToIso (stableFGModuleCatEquivalence_functor A)) ≪≫
      ((stableConflationExact_toFGModuleCat A).stableFunctor
        exactStructure_isFrobenius).commShiftIso n ≪≫
      Functor.isoWhiskerRight (eqToIso (stableFGModuleCatEquivalence_functor A)).symm
        (shiftFunctor (CategoryTheory.GorensteinProjective.exactStructure
          (FGModuleCat.{v} A)).ProjectiveStableCategory n) :=
  (rfl)

/-- Shift compatibility for the inverse functor of `stableFGModuleCatEquivalence`. -/
@[instance_reducible]
def stableFGModuleCatEquivalenceInverseCommShift :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableHasShift
    (stableFGModuleCatEquivalence A).inverse.CommShift ℤ := by
  letI := (exactStructure_isFrobenius (A := A)).stableHasShift
  letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
    (C := FGModuleCat.{v} A)).stableHasShift
  letI := stableFGModuleCatEquivalenceFunctorCommShift A
  exact (stableFGModuleCatEquivalence A).commShiftInverse ℤ

/-- `stableFGModuleCatEquivalenceInverseCommShift` is the mate shift structure
`Equivalence.commShiftInverse` attached to `stableFGModuleCatEquivalenceFunctorCommShift`. -/
theorem stableFGModuleCatEquivalenceInverseCommShift_eq :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableHasShift
    letI := stableFGModuleCatEquivalenceFunctorCommShift A
    stableFGModuleCatEquivalenceInverseCommShift A =
      (stableFGModuleCatEquivalence A).commShiftInverse ℤ :=
  (rfl)

/-- The shift comparison of `(stableFGModuleCatEquivalence A).inverse` agrees with that of
`(stableFGModuleCatEquivalence A).commShiftInverse ℤ`. -/
theorem stableFGModuleCatEquivalenceInverse_commShiftIso (n : ℤ) :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableHasShift
    letI := stableFGModuleCatEquivalenceFunctorCommShift A
    (letI := stableFGModuleCatEquivalenceInverseCommShift A;
      (stableFGModuleCatEquivalence A).inverse.commShiftIso n) =
      (letI := (stableFGModuleCatEquivalence A).commShiftInverse ℤ;
        (stableFGModuleCatEquivalence A).inverse.commShiftIso n) :=
  (rfl)

/-- `stableFGModuleCatEquivalence` is a triangle equivalence for Happel's triangulations. -/
theorem stableFGModuleCatEquivalence_isTriangulated :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableHasShift
    letI := (exactStructure_isFrobenius (A := A)).stableShiftFunctor_additive
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableShiftFunctor_additive
    letI := (exactStructure_isFrobenius (A := A)).stablePretriangulated
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stablePretriangulated
    letI := stableFGModuleCatEquivalenceFunctorCommShift A
    letI := stableFGModuleCatEquivalenceInverseCommShift A
    letI := (stableFGModuleCatEquivalence A).commShift_of_functor ℤ
    (stableFGModuleCatEquivalence A).IsTriangulated := by
  let := (exactStructure_isFrobenius (A := A)).stableHasShift
  let := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
    (C := FGModuleCat.{v} A)).stableHasShift
  let := (exactStructure_isFrobenius (A := A)).stableShiftFunctor_additive
  let := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
    (C := FGModuleCat.{v} A)).stableShiftFunctor_additive
  let := (exactStructure_isFrobenius (A := A)).stablePretriangulated
  let := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
    (C := FGModuleCat.{v} A)).stablePretriangulated
  let := (stableConflationExact_toFGModuleCat A).stableFunctorCommShift
    exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
  have := (stableConflationExact_toFGModuleCat A).stableFunctorIsTriangulated
    exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
  exact (stableFGModuleCatEquivalence A).isTriangulated_of_functor_eq
    (stableFGModuleCatEquivalence_functor A)

/-! ### Chen's functor and Buchweitz's equivalence for `GorensteinProjectiveModuleCat` -/

section Singularity

variable [HasDerivedCategory.{w} (FGModuleCat.{v} A)]

/-- **Chen's functor** on the projective stable category of `GorensteinProjectiveModuleCat A`,
placing a finitely generated Gorenstein-projective `A`-module in degree zero of the singularity
category `D_sg(mod-A)`. -/
def toSingularityCategory :
    (exactStructure.{v} A).ProjectiveStableCategory ⥤
      SingularityCategory (FGModuleCat.{v} A) :=
  (stableFGModuleCatEquivalence A).functor ⋙
    CategoryTheory.GorensteinProjective.toSingularityCategory (FGModuleCat.{v} A)

/-- `toSingularityCategory` factors as `(stableFGModuleCatEquivalence A).functor` followed by
`CategoryTheory.GorensteinProjective.toSingularityCategory (FGModuleCat A)`. -/
theorem toSingularityCategory_def :
    toSingularityCategory.{w, v} A =
      (stableFGModuleCatEquivalence A).functor ⋙
        CategoryTheory.GorensteinProjective.toSingularityCategory (FGModuleCat.{v} A) :=
  (rfl)

instance : (toSingularityCategory.{w, v} A).Additive := by
  rw [toSingularityCategory_def]
  infer_instance

instance : (toSingularityCategory.{w, v} A).Full := by
  rw [toSingularityCategory_def]
  infer_instance

instance : (toSingularityCategory.{w, v} A).Faithful := by
  rw [toSingularityCategory_def]
  infer_instance

/-- **Chen's theorem** for `GorensteinProjectiveModuleCat A`: the functor to `D_sg(mod-A)` is fully
faithful over any left noetherian ring. -/
def fullyFaithfulToSingularityCategory :
    (toSingularityCategory.{w, v} A).FullyFaithful :=
  .ofFullyFaithful _

/-- Along the projective stable quotient functor, `toSingularityCategory` restricts to
`toFGModuleCat` followed by placing objects of `FGModuleCat A` in degree zero of `D_sg(mod-A)`. -/
theorem projectiveStableFunctor_comp_toSingularityCategory :
    (exactStructure.{v} A).projectiveStableFunctor ⋙ toSingularityCategory.{w, v} A =
      toFGModuleCat A ⋙
        CategoryTheory.GorensteinProjective.toSingularityCategoryFunctor (FGModuleCat.{v} A) := by
  rw [toSingularityCategory_def, ← Functor.assoc,
    projectiveStableFunctor_comp_stableFGModuleCatEquivalence_functor, Functor.assoc,
    CategoryTheory.GorensteinProjective.projectiveStableFunctor_comp_toSingularityCategory]

variable {A} in
/-- `toSingularityCategory` sends the stable class of a Gorenstein-projective module `X` to `X`
placed in degree zero in `D_sg(mod-A)`. -/
@[simp]
theorem toSingularityCategory_obj_projectiveStableFunctor_obj
    (X : GorensteinProjectiveModuleCat.{v} A) :
    (toSingularityCategory.{w, v} A).obj ((exactStructure A).projectiveStableFunctor.obj X) =
      (SingularityCategory.Q (FGModuleCat.{v} A)).obj
        ((DerivedCategory.Bounded.singleFunctor (FGModuleCat.{v} A) 0).obj
          ⟨X.obj, (ModuleCat.isFG_iff _).2 X.property.finite⟩) := by
  rw [toSingularityCategory_def, Functor.comp_obj,
    stableFGModuleCatEquivalence_functor_obj_projectiveStableFunctor_obj,
    CategoryTheory.GorensteinProjective.toSingularityCategory_obj_projectiveStableFunctor_obj,
    toFGModuleCat_obj_obj]

variable {A} in
/-- `toSingularityCategory` sends the stable class of a morphism `f` of Gorenstein-projective
modules to `f` placed in degree zero in `D_sg(mod-A)`. -/
@[simp]
theorem toSingularityCategory_map_projectiveStableFunctor_map
    {X Y : GorensteinProjectiveModuleCat.{v} A} (f : X ⟶ Y) :
    (toSingularityCategory.{w, v} A).map ((exactStructure A).projectiveStableFunctor.map f) =
      eqToHom (toSingularityCategory_obj_projectiveStableFunctor_obj X) ≫
        (SingularityCategory.Q (FGModuleCat.{v} A)).map
          ((DerivedCategory.Bounded.singleFunctor (FGModuleCat.{v} A) 0).map
            (ObjectProperty.homMk f.hom :
              (⟨X.obj, (ModuleCat.isFG_iff _).2 X.property.finite⟩ : FGModuleCat.{v} A) ⟶
                ⟨Y.obj, (ModuleCat.isFG_iff _).2 Y.property.finite⟩)) ≫
        eqToHom (toSingularityCategory_obj_projectiveStableFunctor_obj Y).symm :=
  Functor.congr_hom (projectiveStableFunctor_comp_toSingularityCategory.{w, v} A) f

/-- Shift compatibility for `toSingularityCategory`. -/
@[instance_reducible]
def toSingularityCategoryCommShift :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    (toSingularityCategory.{w, v} A).CommShift ℤ := by
  letI := (exactStructure_isFrobenius (A := A)).stableHasShift
  letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
    (C := FGModuleCat.{v} A)).stableHasShift
  letI := stableFGModuleCatEquivalenceFunctorCommShift A
  letI := CategoryTheory.GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{v} A)
  exact Functor.CommShift.ofIso (eqToIso (toSingularityCategory_def.{w, v} A).symm) ℤ

/-- The shift comparison of `toSingularityCategory` is the composite shift comparison of
`(stableFGModuleCatEquivalence A).functor` and
`CategoryTheory.GorensteinProjective.toSingularityCategory (FGModuleCat A)`. -/
theorem toSingularityCategory_commShiftIso (n : ℤ) :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableHasShift
    letI := stableFGModuleCatEquivalenceFunctorCommShift A
    letI := CategoryTheory.GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{v} A)
    letI := toSingularityCategoryCommShift.{w, v} A
    (toSingularityCategory.{w, v} A).commShiftIso n =
      Functor.isoWhiskerLeft (shiftFunctor (exactStructure.{v} A).ProjectiveStableCategory n)
        (eqToIso (toSingularityCategory_def.{w, v} A)) ≪≫
      ((stableFGModuleCatEquivalence A).functor ⋙
        CategoryTheory.GorensteinProjective.toSingularityCategory
          (FGModuleCat.{v} A)).commShiftIso n ≪≫
      Functor.isoWhiskerRight (eqToIso (toSingularityCategory_def.{w, v} A)).symm
        (shiftFunctor (SingularityCategory (FGModuleCat.{v} A)) n) :=
  (rfl)

/-- **Chen's functor on `GorensteinProjectiveModuleCat A` is a triangle functor.** -/
theorem toSingularityCategory_isTriangulated :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (exactStructure_isFrobenius (A := A)).stableShiftFunctor_additive
    letI := (exactStructure_isFrobenius (A := A)).stablePretriangulated
    letI := toSingularityCategoryCommShift.{w, v} A
    (toSingularityCategory.{w, v} A).IsTriangulated := by
  let := (exactStructure_isFrobenius (A := A)).stableHasShift
  let := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
    (C := FGModuleCat.{v} A)).stableHasShift
  let := (exactStructure_isFrobenius (A := A)).stableShiftFunctor_additive
  let := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
    (C := FGModuleCat.{v} A)).stableShiftFunctor_additive
  let := (exactStructure_isFrobenius (A := A)).stablePretriangulated
  let := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
    (C := FGModuleCat.{v} A)).stablePretriangulated
  let := stableFGModuleCatEquivalenceFunctorCommShift A
  let := stableFGModuleCatEquivalenceInverseCommShift A
  let := (stableFGModuleCatEquivalence A).commShift_of_functor ℤ
  have := stableFGModuleCatEquivalence_isTriangulated A
  let := CategoryTheory.GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{v} A)
  have := CategoryTheory.GorensteinProjective.toSingularityCategory_isTriangulated
    (C := FGModuleCat.{v} A)
  let := toSingularityCategoryCommShift.{w, v} A
  have := Functor.CommShift.ofIso_compatibility
    (eqToIso (toSingularityCategory_def.{w, v} A).symm) ℤ
  exact Functor.isTriangulated_of_iso (eqToIso (toSingularityCategory_def.{w, v} A).symm)

end Singularity

end Noetherian

section Buchweitz

variable (A : Type u) [Ring A] [IsIwanagaGorenstein A] [HasDerivedCategory.{w} (FGModuleCat.{u} A)]

/-- **Buchweitz's theorem** for `GorensteinProjectiveModuleCat A`: over an Iwanaga–Gorenstein ring,
`toSingularityCategory` is an equivalence of categories. -/
instance isEquivalence_toSingularityCategory :
    (toSingularityCategory.{w, u} A).IsEquivalence := by
  rw [toSingularityCategory_def]
  infer_instance

/-- **Buchweitz's equivalence**: the equivalence
`(exactStructure A).ProjectiveStableCategory ≌ SingularityCategory (FGModuleCat A)` over an
Iwanaga–Gorenstein ring `A`. -/
def singularityEquivalence :
    (exactStructure.{u} A).ProjectiveStableCategory ≌
      SingularityCategory (FGModuleCat.{u} A) :=
  (toSingularityCategory.{w, u} A).asEquivalence

/-- The forward functor of `singularityEquivalence` is `toSingularityCategory`. -/
@[simp]
theorem singularityEquivalence_functor :
    (singularityEquivalence.{w, u} A).functor = toSingularityCategory.{w, u} A :=
  (rfl)

/-- **Buchweitz's equivalence is triangulated.** -/
theorem singularityEquivalence_isTriangulated :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (exactStructure_isFrobenius (A := A)).stableShiftFunctor_additive
    letI := (exactStructure_isFrobenius (A := A)).stablePretriangulated
    letI := toSingularityCategoryCommShift.{w, u} A
    letI : (singularityEquivalence.{w, u} A).functor.CommShift ℤ :=
      Functor.CommShift.ofIso (eqToIso (singularityEquivalence_functor.{w, u} A).symm) ℤ
    letI := (singularityEquivalence.{w, u} A).commShiftInverse ℤ
    letI := (singularityEquivalence.{w, u} A).commShift_of_functor ℤ
    (singularityEquivalence.{w, u} A).IsTriangulated := by
  let := (exactStructure_isFrobenius (A := A)).stableHasShift
  let := (exactStructure_isFrobenius (A := A)).stableShiftFunctor_additive
  let := (exactStructure_isFrobenius (A := A)).stablePretriangulated
  let := toSingularityCategoryCommShift.{w, u} A
  have := toSingularityCategory_isTriangulated.{w, u} A
  exact (singularityEquivalence.{w, u} A).isTriangulated_of_functor_eq
    (singularityEquivalence_functor.{w, u} A)

end Buchweitz

end TauCeti.GorensteinProjectiveModuleCat
