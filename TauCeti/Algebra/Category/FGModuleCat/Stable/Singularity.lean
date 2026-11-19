/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Stable.Basic
public import TauCeti.Algebra.Homology.GorensteinProjective.Buchweitz
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Frobenius.Abelian
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.Triangulated

/-!
# The stable module category of a self-injective algebra is its singularity category

Let `A` be a finite-dimensional algebra over a field which is self-injective on both sides. Its
stable module category `stmod-A` (`TauCeti.FGModuleCat.stableModuleCategory`, finitely generated
right modules modulo the maps factoring through projectives, triangulated by Happel's theorem) is
triangle equivalent to the singularity category `D_sg(A) = Dᵇ(mod-A) / Kᵇ(proj-A)`:
`TauCeti.FGModuleCat.stableModuleCategoryToSingularityCategory` places a module in degree zero.

This is the specialization of Buchweitz's theorem to self-injective algebras:

1. `A` is Iwanaga–Gorenstein, with both self-injective dimensions zero
   (`TauCeti.IsIwanagaGorenstein.of_injective`);
2. the abelian exact structure of `mod-A` is Frobenius (`FGModuleCat.abelian_isFrobenius`), so every
   finitely generated module is Gorenstein-projective, and `stmod-A` is the stable category of the
   Gorenstein-projective modules
   (`CategoryTheory.GorensteinProjective.stableEquivalenceOfIsFrobenius`);
3. Chen's functor from that stable category to `D_sg(A)` is a triangle equivalence
   (`TauCeti.IsIwanagaGorenstein.isEquivalence_toSingularityCategory`,
   `CategoryTheory.GorensteinProjective.toSingularityCategory_isTriangulated`).

Right `A`-modules are left `Aᵐᵒᵖ`-modules, so the singularity category is that of
`FGModuleCat Aᵐᵒᵖ`, and the self-injectivity hypotheses are stated for `Aᵐᵒᵖ`, as in
`FGModuleCat.abelian_isFrobenius`.

## Main definitions

* `TauCeti.FGModuleCat.stableModuleCategoryToSingularityCategory`: the functor
  `stmod-A ⥤ D_sg(A)`.
* `TauCeti.FGModuleCat.stableModuleCategoryToSingularityCategoryCommShift`: its commutation with
  the shifts.

## Main results

* `TauCeti.FGModuleCat.stableModuleFunctor_comp_stableModuleCategoryToSingularityCategory`: the
  functor places a module in degree zero; on objects and morphisms of `mod-A` this is
  `stableModuleCategoryToSingularityCategory_obj_stableModuleFunctor_obj` and
  `stableModuleCategoryToSingularityCategory_map_stableModuleFunctor_map`.
* `TauCeti.FGModuleCat.isEquivalence_stableModuleCategoryToSingularityCategory`: it is an
  equivalence of categories.
* `TauCeti.FGModuleCat.stableModuleCategoryToSingularityCategory_def_commShift`: its shift
  comparison `stableModuleCategoryToSingularityCategoryCommShift` is that of the composite in its
  definition.
* `TauCeti.FGModuleCat.stableModuleCategoryToSingularityCategory_isTriangulated`: it is a triangle
  functor, so `stmod-A ≃ D_sg(A)` as triangulated categories.

## References

* Ragnar-Olaf Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, Mathematical
  Surveys and Monographs **262**, American Mathematical Society (2021), Theorem 4.4.1.
* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

open CategoryTheory

universe w w' u

namespace TauCeti.FGModuleCat

variable (k : Type w) [Field k] {A : Type u} [Ring A] [Algebra k A] [FiniteDimensional k A]
  [IsNoetherianRing Aᵐᵒᵖ] (hr : Module.Injective Aᵐᵒᵖ Aᵐᵒᵖ)
  (hl : Module.Injective (Aᵐᵒᵖ)ᵐᵒᵖ Aᵐᵒᵖ) [HasDerivedCategory.{w'} (FGModuleCat.{u} Aᵐᵒᵖ)]

/-- The functor `stmod-A ⥤ D_sg(A)` for a finite-dimensional algebra `A` that is self-injective on
both sides: a finitely generated right module is placed in degree zero. It is the inverse of the
identification of `stmod-A` with the stable category of Gorenstein-projective modules, followed by
Chen's functor. -/
noncomputable def stableModuleCategoryToSingularityCategory :
    stableModuleCategory A ⥤ SingularityCategory (FGModuleCat.{u} Aᵐᵒᵖ) :=
  (GorensteinProjective.stableEquivalenceOfIsFrobenius
      (FGModuleCat.abelian_isFrobenius k hr hl)).inverse ⋙
    GorensteinProjective.toSingularityCategory (FGModuleCat.{u} Aᵐᵒᵖ)

/-- The defining equation of `stableModuleCategoryToSingularityCategory`. -/
theorem stableModuleCategoryToSingularityCategory_def :
    stableModuleCategoryToSingularityCategory k hr hl =
      (GorensteinProjective.stableEquivalenceOfIsFrobenius
          (FGModuleCat.abelian_isFrobenius k hr hl)).inverse ⋙
        GorensteinProjective.toSingularityCategory (FGModuleCat.{u} Aᵐᵒᵖ) :=
  (rfl)

instance : (stableModuleCategoryToSingularityCategory k hr hl).Additive := by
  rw [stableModuleCategoryToSingularityCategory_def]
  infer_instance

/-- The functor `stmod-A ⥤ D_sg(A)` restricts along the quotient functor `mod-A ⥤ stmod-A` to
placing a module in degree zero. -/
theorem stableModuleFunctor_comp_stableModuleCategoryToSingularityCategory :
    stableModuleFunctor A ⋙ stableModuleCategoryToSingularityCategory k hr hl =
      DerivedCategory.Bounded.singleFunctor (FGModuleCat.{u} Aᵐᵒᵖ) 0 ⋙
        SingularityCategory.Q (FGModuleCat.{u} Aᵐᵒᵖ) := by
  rw [stableModuleCategoryToSingularityCategory_def,
    StableConflationExact.stableEquivalence_inverse, StableConflationExact.stableFunctor_eq_map,
    ← Functor.assoc, MorphismIdeal.quotientFunctor_comp_map, Functor.assoc,
    GorensteinProjective.projectiveStableFunctor_comp_toSingularityCategory,
    GorensteinProjective.toSingularityCategoryFunctor, ← Functor.assoc]
  -- The inverse of `equivalenceOfIsFrobenius` is the lift of `𝟭` through the inclusion `ι`, and a
  -- lift followed by `ι` is the original functor by definition (`ObjectProperty.liftCompιIso` is
  -- `Iso.refl`).
  rw [GorensteinProjective.equivalenceOfIsFrobenius_inverse]
  rfl

/-- The functor `stmod-A ⥤ D_sg(A)` places a finitely generated right module in degree zero. -/
@[simp]
theorem stableModuleCategoryToSingularityCategory_obj_stableModuleFunctor_obj
    (M : FGModuleCat.{u} Aᵐᵒᵖ) :
    (stableModuleCategoryToSingularityCategory k hr hl).obj ((stableModuleFunctor A).obj M) =
      (SingularityCategory.Q (FGModuleCat.{u} Aᵐᵒᵖ)).obj
        ((DerivedCategory.Bounded.singleFunctor (FGModuleCat.{u} Aᵐᵒᵖ) 0).obj M) :=
  Functor.congr_obj (stableModuleFunctor_comp_stableModuleCategoryToSingularityCategory k hr hl) M

/-- The functor `stmod-A ⥤ D_sg(A)` places a morphism of finitely generated right modules in
degree zero. -/
@[simp]
theorem stableModuleCategoryToSingularityCategory_map_stableModuleFunctor_map
    {M N : FGModuleCat.{u} Aᵐᵒᵖ} (f : M ⟶ N) :
    (stableModuleCategoryToSingularityCategory k hr hl).map ((stableModuleFunctor A).map f) =
      eqToHom (stableModuleCategoryToSingularityCategory_obj_stableModuleFunctor_obj k hr hl M) ≫
        (SingularityCategory.Q (FGModuleCat.{u} Aᵐᵒᵖ)).map
          ((DerivedCategory.Bounded.singleFunctor (FGModuleCat.{u} Aᵐᵒᵖ) 0).map f) ≫
        eqToHom (stableModuleCategoryToSingularityCategory_obj_stableModuleFunctor_obj k hr hl
          N).symm :=
  Functor.congr_hom (stableModuleFunctor_comp_stableModuleCategoryToSingularityCategory k hr hl) f

/-- **Buchweitz's theorem for self-injective algebras**: the functor `stmod-A ⥤ D_sg(A)` is an
equivalence of categories. -/
instance isEquivalence_stableModuleCategoryToSingularityCategory :
    (stableModuleCategoryToSingularityCategory k hr hl).IsEquivalence := by
  -- `A` is Iwanaga–Gorenstein as a ring acting on right modules.
  have : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ := isNoetherian_of_tower k inferInstance
  have := hr
  have := hl
  have := IsIwanagaGorenstein.of_injective Aᵐᵒᵖ
  rw [stableModuleCategoryToSingularityCategory_def]
  infer_instance

/-- The Happel triangulation of `stmod-A`, from the Frobenius exact structure of `mod-A`. -/
local notation "hE" => (FGModuleCat.abelian_isFrobenius k hr hl)

/-- The commutation of `stableModuleCategoryToSingularityCategory` with the shifts: that of the
inverse of the identification of `stmod-A` with the stable category of Gorenstein-projective
modules, followed by that of Chen's functor. -/
@[instance_reducible]
noncomputable def stableModuleCategoryToSingularityCategoryCommShift :
    letI := (hE).stableHasShift
    (stableModuleCategoryToSingularityCategory k hr hl).CommShift ℤ := by
  let hE' : (ExactStructure.abelian (FGModuleCat.{u} Aᵐᵒᵖ)).IsFrobenius := hE
  let hG := GorensteinProjective.exactStructure_isFrobenius (C := FGModuleCat.{u} Aᵐᵒᵖ)
  let := hE'.stableHasShift
  let := hG.stableHasShift
  let := StableConflationExact.stableEquivalenceInverseCommShift
    (GorensteinProjective.stableConflationExact_equivalenceOfIsFrobenius_functor hE')
    (GorensteinProjective.stableConflationExact_equivalenceOfIsFrobenius_inverse hE') hG hE'
  let := GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{u} Aᵐᵒᵖ)
  unfold stableModuleCategoryToSingularityCategory
  infer_instance

/-- **Shift compatibility**: the identification `stableModuleCategoryToSingularityCategory_def` of
the functor `stmod-A ⥤ D_sg(A)` with the inverse of the identification of `stmod-A` with the stable
category of Gorenstein-projective modules, followed by Chen's functor, commutes with the shifts:
`stableModuleCategoryToSingularityCategoryCommShift` is the composite of their shift
comparisons. -/
theorem stableModuleCategoryToSingularityCategory_def_commShift :
    letI := (hE).stableHasShift
    letI := (GorensteinProjective.exactStructure_isFrobenius
      (C := FGModuleCat.{u} Aᵐᵒᵖ)).stableHasShift
    letI := StableConflationExact.stableEquivalenceInverseCommShift
      (GorensteinProjective.stableConflationExact_equivalenceOfIsFrobenius_functor hE)
      (GorensteinProjective.stableConflationExact_equivalenceOfIsFrobenius_inverse hE)
      GorensteinProjective.exactStructure_isFrobenius hE
    letI := GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{u} Aᵐᵒᵖ)
    letI := stableModuleCategoryToSingularityCategoryCommShift k hr hl
    (eqToIso (stableModuleCategoryToSingularityCategory_def k hr hl)).hom.CommShift ℤ := by
  let hE' : (ExactStructure.abelian (FGModuleCat.{u} Aᵐᵒᵖ)).IsFrobenius := hE
  let hG := GorensteinProjective.exactStructure_isFrobenius (C := FGModuleCat.{u} Aᵐᵒᵖ)
  let := hE'.stableHasShift
  let := hG.stableHasShift
  let := StableConflationExact.stableEquivalenceInverseCommShift
    (GorensteinProjective.stableConflationExact_equivalenceOfIsFrobenius_functor hE')
    (GorensteinProjective.stableConflationExact_equivalenceOfIsFrobenius_inverse hE') hG hE'
  let := GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{u} Aᵐᵒᵖ)
  -- Both the functor and its shift comparison are the composite ones by definition, so the
  -- identification is the identity.
  exact inferInstanceAs (NatTrans.CommShift (𝟙 ((GorensteinProjective.stableEquivalenceOfIsFrobenius
    hE').inverse ⋙ GorensteinProjective.toSingularityCategory (FGModuleCat.{u} Aᵐᵒᵖ))) ℤ)

/-- **Buchweitz's theorem for self-injective algebras**, triangulated form: the functor
`stmod-A ⥤ D_sg(A)` is a triangle functor for Happel's triangulation of `stmod-A`. Together with
`TauCeti.FGModuleCat.isEquivalence_stableModuleCategoryToSingularityCategory`, it is a triangle
equivalence. -/
theorem stableModuleCategoryToSingularityCategory_isTriangulated :
    letI := (hE).stableHasShift
    letI := (hE).stableShiftFunctor_additive
    letI := (hE).stablePretriangulated
    letI := stableModuleCategoryToSingularityCategoryCommShift k hr hl
    (stableModuleCategoryToSingularityCategory k hr hl).IsTriangulated := by
  let hE' : (ExactStructure.abelian (FGModuleCat.{u} Aᵐᵒᵖ)).IsFrobenius := hE
  let := hE'.stableHasShift
  let := hE'.stableShiftFunctor_additive
  let := hE'.stablePretriangulated
  let hG := GorensteinProjective.exactStructure_isFrobenius (C := FGModuleCat.{u} Aᵐᵒᵖ)
  let := hG.stableHasShift
  let := hG.stableShiftFunctor_additive
  let := hG.stablePretriangulated
  let hF := GorensteinProjective.stableConflationExact_equivalenceOfIsFrobenius_functor hE'
  let hI := GorensteinProjective.stableConflationExact_equivalenceOfIsFrobenius_inverse hE'
  let := StableConflationExact.stableEquivalenceFunctorCommShift hF hI hG hE'
  let := StableConflationExact.stableEquivalenceInverseCommShift hF hI hG hE'
  let := GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{u} Aᵐᵒᵖ)
  have := GorensteinProjective.stableEquivalenceOfIsFrobenius_isTriangulated hE'
  have := GorensteinProjective.toSingularityCategory_isTriangulated (C := FGModuleCat.{u} Aᵐᵒᵖ)
  let := stableModuleCategoryToSingularityCategoryCommShift k hr hl
  unfold stableModuleCategoryToSingularityCategory
  infer_instance

end TauCeti.FGModuleCat
