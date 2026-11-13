/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Stable.Basic
public import TauCeti.Algebra.Homology.GorensteinProjective.Buchweitz
public import TauCeti.Algebra.Homology.TotallyAcyclic.Abelian.FrobeniusAbelian
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

## Main results

* `TauCeti.FGModuleCat.isIwanagaGorenstein_op`: `A` is Iwanaga–Gorenstein as a ring acting on
  right modules.
* `TauCeti.FGModuleCat.stableModuleCategoryToSingularityCategory_obj_stableModuleFunctor_obj`: the
  functor places a module in degree zero.
* `TauCeti.FGModuleCat.isEquivalence_stableModuleCategoryToSingularityCategory`: it is an
  equivalence of categories.
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
  (hl : Module.Injective (Aᵐᵒᵖ)ᵐᵒᵖ Aᵐᵒᵖ)

include k hr hl in
/-- A finite-dimensional algebra which is self-injective on both sides is Iwanaga–Gorenstein, as a
ring acting on right modules. -/
theorem isIwanagaGorenstein_op : IsIwanagaGorenstein Aᵐᵒᵖ := by
  have : IsNoetherianRing (Aᵐᵒᵖ)ᵐᵒᵖ := isNoetherian_of_tower k inferInstance
  have := hr
  have := hl
  exact IsIwanagaGorenstein.of_injective Aᵐᵒᵖ

variable [HasDerivedCategory.{w'} (FGModuleCat.{u} Aᵐᵒᵖ)]

/-- The functor `stmod-A ⥤ D_sg(A)` for a finite-dimensional algebra `A` that is self-injective on
both sides: a finitely generated right module is placed in degree zero. It is the inverse of the
identification of `stmod-A` with the stable category of Gorenstein-projective modules, followed by
Chen's functor. -/
noncomputable def stableModuleCategoryToSingularityCategory :
    stableModuleCategory A ⥤ SingularityCategory (FGModuleCat.{u} Aᵐᵒᵖ) :=
  (GorensteinProjective.stableEquivalenceOfIsFrobenius
      (FGModuleCat.abelian_isFrobenius k hr hl)).inverse ⋙
    GorensteinProjective.toSingularityCategory (FGModuleCat.{u} Aᵐᵒᵖ)

/-- The functor `stmod-A ⥤ D_sg(A)` places a finitely generated right module in degree zero. -/
theorem stableModuleCategoryToSingularityCategory_obj_stableModuleFunctor_obj
    (M : FGModuleCat.{u} Aᵐᵒᵖ) :
    (stableModuleCategoryToSingularityCategory k hr hl).obj ((stableModuleFunctor A).obj M) =
      (SingularityCategory.Q (FGModuleCat.{u} Aᵐᵒᵖ)).obj
        ((DerivedCategory.Bounded.singleFunctor (FGModuleCat.{u} Aᵐᵒᵖ) 0).obj M) := by
  rw [stableModuleCategoryToSingularityCategory, Functor.comp_obj,
    StableConflationExact.stableEquivalence_inverse,
    StableConflationExact.stableFunctor_obj_projectiveStableFunctor_obj,
    GorensteinProjective.toSingularityCategory_obj_projectiveStableFunctor_obj]
  rfl

/-- **Buchweitz's theorem for self-injective algebras**: the functor `stmod-A ⥤ D_sg(A)` is an
equivalence of categories. -/
instance isEquivalence_stableModuleCategoryToSingularityCategory :
    (stableModuleCategoryToSingularityCategory k hr hl).IsEquivalence := by
  have := isIwanagaGorenstein_op k hr hl
  dsimp [stableModuleCategoryToSingularityCategory]
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
  let := (GorensteinProjective.stableEquivalenceOfIsFrobenius hE').commShift_of_functor ℤ
  let := GorensteinProjective.toSingularityCategoryCommShift (FGModuleCat.{u} Aᵐᵒᵖ)
  have := GorensteinProjective.stableEquivalenceOfIsFrobenius_isTriangulated hE'
  have := GorensteinProjective.toSingularityCategory_isTriangulated (C := FGModuleCat.{u} Aᵐᵒᵖ)
  let := stableModuleCategoryToSingularityCategoryCommShift k hr hl
  unfold stableModuleCategoryToSingularityCategory
  infer_instance

end TauCeti.FGModuleCat
