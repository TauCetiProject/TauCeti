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

/-- Composing `fromFGModuleCat` with `(IsGorensteinProjective A).ι` forgets Gorenstein projectivity
and finite generation. -/
theorem fromFGModuleCat_comp_ι :
    fromFGModuleCat.{v} A ⋙ (IsGorensteinProjective A).ι =
      (CategoryTheory.isGorensteinProjective (FGModuleCat.{v} A)).ι ⋙
        forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) :=
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
    rw [exactStructure_conflation_iff] at hS
    rw [CategoryTheory.GorensteinProjective.exactStructure_conflation_iff]
    let F := forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)
    let S' := S.map (toFGModuleCat A ⋙
      (CategoryTheory.isGorensteinProjective (FGModuleCat.{v} A)).ι)
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
    rw [exactStructure_conflation_iff]
    exact hS.map_of_exact (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A))

private theorem stableConflationExact_functor :
    StableConflationExact (exactStructure.{v} A)
      (CategoryTheory.GorensteinProjective.exactStructure (FGModuleCat.{v} A))
      (fgModuleCatEquivalence A).functor :=
  ExactStructure.IsConflationExact.stableConflationExact_of_equivalence
    (e := fgModuleCatEquivalence A)
    (by dsimp only [fgModuleCatEquivalence]; exact isConflationExact_toFGModuleCat A)
    (by dsimp only [fgModuleCatEquivalence]; exact isConflationExact_fromFGModuleCat A)

private theorem stableConflationExact_inverse :
    StableConflationExact
      (CategoryTheory.GorensteinProjective.exactStructure (FGModuleCat.{v} A))
      (exactStructure.{v} A) (fgModuleCatEquivalence A).inverse := by
  have : (fgModuleCatEquivalence A).symm.functor.Additive := by
    dsimp only [Equivalence.symm_functor]
    infer_instance
  exact ExactStructure.IsConflationExact.stableConflationExact_of_equivalence
    (e := (fgModuleCatEquivalence A).symm)
    (by dsimp only [Equivalence.symm_functor, fgModuleCatEquivalence]
        exact isConflationExact_fromFGModuleCat A)
    (by dsimp only [Equivalence.symm_inverse, fgModuleCatEquivalence]
        exact isConflationExact_toFGModuleCat A)

/-- `toFGModuleCat` preserves conflations and projective-injectives. -/
theorem stableConflationExact_toFGModuleCat :
    StableConflationExact (exactStructure.{v} A)
      (CategoryTheory.GorensteinProjective.exactStructure (FGModuleCat.{v} A))
      (toFGModuleCat A) := by
  simpa only [fgModuleCatEquivalence] using stableConflationExact_functor A

/-- `fromFGModuleCat` preserves conflations and projective-injectives. -/
theorem stableConflationExact_fromFGModuleCat :
    StableConflationExact
      (CategoryTheory.GorensteinProjective.exactStructure (FGModuleCat.{v} A))
      (exactStructure.{v} A) (fromFGModuleCat A) := by
  simpa only [fgModuleCatEquivalence] using stableConflationExact_inverse A

/-- The projective stable equivalence between `GorensteinProjectiveModuleCat A` and
`CategoryTheory.GorensteinProjective (FGModuleCat A)`. -/
def stableFGModuleCatEquivalence :
    (exactStructure.{v} A).ProjectiveStableCategory ≌
      (CategoryTheory.GorensteinProjective.exactStructure
        (FGModuleCat.{v} A)).ProjectiveStableCategory :=
  StableConflationExact.stableEquivalence (fgModuleCatEquivalence A)
    (stableConflationExact_functor A) (stableConflationExact_inverse A)
    exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius

instance : (stableFGModuleCatEquivalence A).functor.Additive := by
  rw [stableFGModuleCatEquivalence, StableConflationExact.stableEquivalence_functor,
    StableConflationExact.stableFunctor_eq_map]
  infer_instance

instance : (stableFGModuleCatEquivalence A).inverse.Additive := by
  rw [stableFGModuleCatEquivalence, StableConflationExact.stableEquivalence_inverse,
    StableConflationExact.stableFunctor_eq_map]
  infer_instance

/-- On `GorensteinProjectiveModuleCat A`, `stableFGModuleCatEquivalence` intertwines the projective
stable quotient functors with `toFGModuleCat`. -/
theorem projectiveStableFunctor_comp_stableFGModuleCatEquivalence_functor :
    (exactStructure.{v} A).projectiveStableFunctor ⋙ (stableFGModuleCatEquivalence A).functor =
      toFGModuleCat A ⋙
        (CategoryTheory.GorensteinProjective.exactStructure
          (FGModuleCat.{v} A)).projectiveStableFunctor := by
  rw [stableFGModuleCatEquivalence, StableConflationExact.stableEquivalence_functor,
    StableConflationExact.stableFunctor_eq_map, MorphismIdeal.quotientFunctor_comp_map,
    fgModuleCatEquivalence_functor]

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
        ((exactStructure A).projectiveStableFunctor.map f) ≫
      eqToHom (stableFGModuleCatEquivalence_functor_obj_projectiveStableFunctor_obj Y) =
    eqToHom (stableFGModuleCatEquivalence_functor_obj_projectiveStableFunctor_obj X) ≫
      (CategoryTheory.GorensteinProjective.exactStructure
        (FGModuleCat.{v} A)).projectiveStableFunctor.map ((toFGModuleCat A).map f) := by
  have h := Functor.congr_hom
    (projectiveStableFunctor_comp_stableFGModuleCatEquivalence_functor A) f
  simp only [Functor.comp_obj, Functor.comp_map] at h
  rw [h, Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- Shift compatibility for the forward functor of `stableFGModuleCatEquivalence`. -/
@[instance_reducible]
def stableFGModuleCatEquivalenceFunctorCommShift :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableHasShift
    (stableFGModuleCatEquivalence A).functor.CommShift ℤ := by
  unfold stableFGModuleCatEquivalence
  exact StableConflationExact.stableEquivalenceFunctorCommShift
    (stableConflationExact_functor A) (stableConflationExact_inverse A)
    exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius

/-- Shift compatibility for the inverse functor of `stableFGModuleCatEquivalence`. -/
@[instance_reducible]
def stableFGModuleCatEquivalenceInverseCommShift :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    letI := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{v} A)).stableHasShift
    (stableFGModuleCatEquivalence A).inverse.CommShift ℤ := by
  unfold stableFGModuleCatEquivalence
  exact StableConflationExact.stableEquivalenceInverseCommShift
    (stableConflationExact_functor A) (stableConflationExact_inverse A)
    exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius

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
  unfold stableFGModuleCatEquivalence stableFGModuleCatEquivalenceFunctorCommShift
    stableFGModuleCatEquivalenceInverseCommShift
  exact StableConflationExact.stableEquivalenceIsTriangulated
    (stableConflationExact_functor A) (stableConflationExact_inverse A)
    exactStructure_isFrobenius CategoryTheory.GorensteinProjective.exactStructure_isFrobenius

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

instance : (toSingularityCategory.{w, v} A).Additive := by
  unfold toSingularityCategory
  infer_instance

instance : (toSingularityCategory.{w, v} A).Full := by
  unfold toSingularityCategory
  infer_instance

instance : (toSingularityCategory.{w, v} A).Faithful := by
  unfold toSingularityCategory
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
  unfold toSingularityCategory
  rw [← Functor.assoc, projectiveStableFunctor_comp_stableFGModuleCatEquivalence_functor,
    Functor.assoc,
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
  unfold toSingularityCategory
  rw [Functor.comp_obj, stableFGModuleCatEquivalence_functor_obj_projectiveStableFunctor_obj,
    CategoryTheory.GorensteinProjective.toSingularityCategory_obj_projectiveStableFunctor_obj]
  rfl

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
        eqToHom (toSingularityCategory_obj_projectiveStableFunctor_obj Y).symm := by
  have h := congrArg
    (CategoryTheory.GorensteinProjective.toSingularityCategory (FGModuleCat.{v} A)).map
    (stableFGModuleCatEquivalence_functor_map_projectiveStableFunctor_map f)
  simp only [Functor.map_comp, eqToHom_map,
    CategoryTheory.GorensteinProjective.toSingularityCategory_map_projectiveStableFunctor_map] at h
  apply (cancel_mono (eqToHom (toSingularityCategory_obj_projectiveStableFunctor_obj Y))).1
  rw [Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact h

/-- Shift compatibility for `toSingularityCategory`. -/
@[instance_reducible]
def toSingularityCategoryCommShift :
    letI := (exactStructure_isFrobenius (A := A)).stableHasShift
    (toSingularityCategory.{w, v} A).CommShift ℤ := by
  let := (exactStructure_isFrobenius (A := A)).stableHasShift
  let := (CategoryTheory.GorensteinProjective.exactStructure_isFrobenius
    (C := FGModuleCat.{v} A)).stableHasShift
  let := stableFGModuleCatEquivalenceFunctorCommShift A
  let := CategoryTheory.GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{v} A)
  unfold toSingularityCategory
  infer_instance

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
  unfold toSingularityCategory
  infer_instance

end Singularity

end Noetherian

section Buchweitz

variable (A : Type u) [Ring A] [IsIwanagaGorenstein A] [HasDerivedCategory.{w} (FGModuleCat.{u} A)]

/-- **Buchweitz's theorem** for `GorensteinProjectiveModuleCat A`: over an Iwanaga–Gorenstein ring,
`toSingularityCategory` is an equivalence of categories. -/
instance isEquivalence_toSingularityCategory :
    (toSingularityCategory.{w, u} A).IsEquivalence := by
  unfold toSingularityCategory
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
  let e := eqToIso (singularityEquivalence_functor.{w, u} A).symm
  let : (singularityEquivalence.{w, u} A).functor.CommShift ℤ := Functor.CommShift.ofIso e ℤ
  let := (singularityEquivalence.{w, u} A).commShiftInverse ℤ
  let := (singularityEquivalence.{w, u} A).commShift_of_functor ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  have := toSingularityCategory_isTriangulated.{w, u} A
  exact Equivalence.IsTriangulated.mk' _ (Functor.isTriangulated_of_iso e)

end Buchweitz

end TauCeti.GorensteinProjectiveModuleCat
