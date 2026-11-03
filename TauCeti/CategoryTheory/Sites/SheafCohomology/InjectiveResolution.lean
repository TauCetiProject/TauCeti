/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.FunctorCategory
public import TauCeti.CategoryTheory.Abelian.Injective.Ext
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda

/-!
# Sheaf cohomology from the sections of an injective resolution

Let `0 ⟶ F ⟶ I⁰ ⟶ I¹ ⟶ ⋯` be an injective resolution of an abelian sheaf `F` on a site `(C, J)`.
For every object `U` of `C`, the complex of sections `I⁰(U) ⟶ I¹(U) ⟶ ⋯` computes the
cohomology `Hⁿ(U, F)`, naturally in `U`. Stated without choosing objects: the homology of the
complex of presheaves underlying `I` is Mathlib's cohomology presheaf
`CategoryTheory.Sheaf.cohomologyPresheaf F n`, which sends `U` to `Hⁿ(U, F)`
(`CategoryTheory.InjectiveResolution.homologyIsoCohomologyPresheaf`).

Mathlib defines `Hⁿ(U, F)` as `Extⁿ(ℤ_U, F)`, where `ℤ_U` is the free abelian sheaf on `U`. A
section `s ∈ Iⁿ(U)` is a morphism `ℤ_U ⟶ Iⁿ`
(`TauCeti.CategoryTheory.freeYonedaSheafSectionsEquiv`), and when `s` is a cycle its class in
`Extⁿ(ℤ_U, F)` is Mathlib's `CategoryTheory.InjectiveResolution.extMk`. Every class arises this
way, and exactly the boundaries have zero class
(`CategoryTheory.InjectiveResolution.extMk_eq_zero_iff` and, in degree zero,
`CategoryTheory.InjectiveResolution.extMk_eq_zero_iff_eq_zero`); restricting sections is
precomposition with the induced map of free abelian sheaves
(`CategoryTheory.Sheaf.cohomologyPresheaf_map_apply`).

This is the computation used to describe higher direct images along a morphism of sites as
sheafified cohomology presheaves.

## Main declarations

* `CategoryTheory.InjectiveResolution.homologyIsoCohomologyPresheaf`: the homology of the complex
  of presheaves underlying an injective resolution of `F` is the cohomology presheaf of `F`.
* `CategoryTheory.InjectiveResolution.homologyIsoCohomologyPresheaf_hom_app_homologyπ_apply`: the
  class of a cycle `s ∈ Iⁿ(U)` is `extMk` of the corresponding morphism `ℤ_U ⟶ Iⁿ`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section III.2.
-/

public section

open CategoryTheory Limits Opposite Abelian TauCeti.CategoryTheory

universe v u

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{v} (Sheaf J AddCommGrpCat.{v})]
  {F : Sheaf J AddCommGrpCat.{v}} (R : InjectiveResolution F) (n : ℕ)

noncomputable section

/-- The complex of presheaves of abelian groups underlying an injective resolution. -/
private abbrev sectionsComplex : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{v}) ℕ :=
  ((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj R.cocomplex

omit [HasExt.{v} (Sheaf J AddCommGrpCat.{v})] in
/-- A cycle in degree `n` of the complex of sections over `U` of an injective resolution `I` is
killed by the differential of `I`. -/
lemma freeYonedaSheafSectionsEquiv_symm_iCycles_app_comp_d {U : C} (m : ℕ)
    (z : ((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj
      R.cocomplex).cycles n).obj (op U)) :
    (freeYonedaSheafSectionsEquiv J U _).symm
      (((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj
        R.cocomplex).iCycles n).app (op U) z) ≫ R.cocomplex.d n m = 0 := by
  apply (freeYonedaSheafSectionsEquiv J U _).injective
  rw [freeYonedaSheafSectionsEquiv_naturality_right, AddEquiv.apply_symm_apply, map_zero]
  have h := congrArg (fun φ ↦ φ.app (op U) z) ((sectionsComplex R).iCycles_d n m)
  simpa using h

/-- The class in `Hⁿ(U, F) = Extⁿ(ℤ_U, F)` of a cycle of the complex of sections over `U`. -/
private def cyclesToH' (U : C) : ((sectionsComplex R).cycles n).obj (op U) →+ F.H' n U :=
  (F.H'AddEquivExt n U).symm.toAddMonoidHom.comp <|
    AddMonoidHom.mk' (fun z ↦ R.extMk ((freeYonedaSheafSectionsEquiv J U _).symm
      (((sectionsComplex R).iCycles n).app (op U) z)) (n + 1) rfl
        (R.freeYonedaSheafSectionsEquiv_symm_iCycles_app_comp_d n _ z))
    (fun z w ↦ by
      rw [R.add_extMk]
      congr 1
      simp)

private lemma H'AddEquivExt_cyclesToH' (U : C) (z : ((sectionsComplex R).cycles n).obj (op U)) :
    F.H'AddEquivExt n U (cyclesToH' R n U z) = R.extMk ((freeYonedaSheafSectionsEquiv J U _).symm
      (((sectionsComplex R).iCycles n).app (op U) z)) (n + 1) rfl
        (R.freeYonedaSheafSectionsEquiv_symm_iCycles_app_comp_d n _ z) := by
  simp [cyclesToH']

private lemma cyclesToH'_naturality {U V : Cᵒᵖ} (g : U ⟶ V)
    (z : ((sectionsComplex R).cycles n).obj U) :
    cyclesToH' R n V.unop (((sectionsComplex R).cycles n).map g z) =
      (F.cohomologyPresheaf n).map g (cyclesToH' R n U.unop z) := by
  apply (F.H'AddEquivExt n V.unop).injective
  have h := F.cohomologyPresheaf_map_apply g.unop n (cyclesToH' R n U.unop z)
  rw [Quiver.Hom.op_unop] at h
  rw [h, H'AddEquivExt_cyclesToH', H'AddEquivExt_cyclesToH', R.mk₀_comp_extMk]
  congr 1
  apply (freeYonedaSheafSectionsEquiv J _ _).injective
  rw [freeYonedaSheafSectionsEquiv_naturality_left, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  simp

/-- The classes of cycles, as a morphism from the presheaf of cycles to the cohomology presheaf. -/
private def cyclesToCohomologyPresheaf :
    (sectionsComplex R).cycles n ⟶ F.cohomologyPresheaf n where
  app U := AddCommGrpCat.ofHom (cyclesToH' R n U.unop)
  naturality U V g := by
    ext z
    exact cyclesToH'_naturality R n g z

private lemma cyclesToH'_toCycles_app (i : ℕ) (hi : i + 1 = n) {U : Cᵒᵖ}
    (x : ((sectionsComplex R).X i).obj U) :
    cyclesToH' R n U.unop (((sectionsComplex R).toCycles i n).app U x) = 0 := by
  apply (F.H'AddEquivExt n U.unop).injective
  rw [H'AddEquivExt_cyclesToH', map_zero (F.H'AddEquivExt n U.unop),
    R.extMk_eq_zero_iff _ _ _ _ i hi]
  refine ⟨(freeYonedaSheafSectionsEquiv J _ _).symm x, ?_⟩
  apply (freeYonedaSheafSectionsEquiv J _ _).injective
  rw [freeYonedaSheafSectionsEquiv_naturality_right, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]
  exact ((sectionsComplex R).iCycles_app_toCycles_app i n x).symm

/-- Boundaries have zero class. -/
private lemma toCycles_comp_cyclesToCohomologyPresheaf (i : ℕ) :
    (sectionsComplex R).toCycles i n ≫ cyclesToCohomologyPresheaf R n = 0 := by
  by_cases hi : (ComplexShape.up ℕ).Rel i n
  · ext U x
    exact cyclesToH'_toCycles_app R n i hi x
  · rw [(sectionsComplex R).toCycles_eq_zero hi, zero_comp]

/-- The comparison map from the homology of the complex of sections to the cohomology presheaf,
induced by the classes of cycles. -/
private def homologyToCohomologyPresheaf :
    (sectionsComplex R).homology n ⟶ F.cohomologyPresheaf n :=
  ((sectionsComplex R).homologyIsCokernel _ n rfl).desc
    (CokernelCofork.ofπ _ (toCycles_comp_cyclesToCohomologyPresheaf R n _))

private lemma homologyπ_comp_homologyToCohomologyPresheaf :
    (sectionsComplex R).homologyπ n ≫ homologyToCohomologyPresheaf R n =
      cyclesToCohomologyPresheaf R n :=
  Cofork.IsColimit.π_desc ((sectionsComplex R).homologyIsCokernel _ n rfl)

private lemma isIso_homologyToCohomologyPresheaf : IsIso (homologyToCohomologyPresheaf R n) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  have hπ : Function.Surjective (((sectionsComplex R).homologyπ n).app U) :=
    (AddCommGrpCat.epi_iff_surjective _).1 inferInstance
  have hi : Function.Injective (((sectionsComplex R).iCycles n).app U) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  have hfac (z : ((sectionsComplex R).cycles n).obj U) :
      (homologyToCohomologyPresheaf R n).app U (((sectionsComplex R).homologyπ n).app U z) =
        cyclesToH' R n U.unop z := by
    have h := ConcreteCategory.congr_hom
      (NatTrans.congr_app (homologyπ_comp_homologyToCohomologyPresheaf R n) U) z
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
    exact h
  refine ⟨(injective_iff_map_eq_zero ((homologyToCohomologyPresheaf R n).app U).hom).2 ?_, ?_⟩
  · intro h hh
    obtain ⟨z, rfl⟩ := hπ h
    rw [hfac] at hh
    apply_fun F.H'AddEquivExt n U.unop at hh
    rw [H'AddEquivExt_cyclesToH', map_zero (F.H'AddEquivExt n U.unop)] at hh
    cases n with
    | zero =>
      rw [R.extMk_eq_zero_iff_eq_zero, AddEquiv.map_eq_zero_iff] at hh
      rw [hi (hh.trans (map_zero _).symm), map_zero]
    | succ p =>
      obtain ⟨g, hg⟩ := (R.extMk_eq_zero_iff _ _ _ _ p rfl).1 hh
      have hz : z = ((sectionsComplex R).toCycles p (p + 1)).app U
          (freeYonedaSheafSectionsEquiv J _ _ g) := by
        apply hi
        rw [HomologicalComplex.iCycles_app_toCycles_app]
        refine Eq.trans ?_
          (freeYonedaSheafSectionsEquiv_naturality_right J g (R.cocomplex.d p (p + 1)))
        rw [hg, AddEquiv.apply_symm_apply]
      rw [hz, ← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
        HomologicalComplex.toCycles_comp_homologyπ, NatTrans.app_zero]
      rfl
  · intro α
    obtain ⟨f, hf, hfα⟩ := R.extMk_surjective (F.H'AddEquivExt n U.unop α) (n + 1) rfl
    obtain ⟨z, hz⟩ := (sectionsComplex R).exists_iCycles_app_eq (n + 1) (by simp)
      (freeYonedaSheafSectionsEquiv J U.unop _ f)
      ((freeYonedaSheafSectionsEquiv_naturality_right J f (R.cocomplex.d n (n + 1))).symm.trans
        (by rw [hf, map_zero]))
    refine ⟨((sectionsComplex R).homologyπ n).app U z, ?_⟩
    rw [hfac]
    apply (F.H'AddEquivExt n U.unop).injective
    rw [H'AddEquivExt_cyclesToH', ← hfα]
    congr 1
    rw [hz, AddEquiv.symm_apply_apply]

/-- **The sections of an injective resolution compute sheaf cohomology.** For an injective
resolution `I` of an abelian sheaf `F`, the homology in degree `n` of the complex of presheaves
`I⁰ ⟶ I¹ ⟶ ⋯` is the cohomology presheaf `U ↦ Hⁿ(U, F)`. -/
def homologyIsoCohomologyPresheaf :
    (((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj R.cocomplex).homology n ≅
      F.cohomologyPresheaf n :=
  haveI := isIso_homologyToCohomologyPresheaf R n
  asIso (homologyToCohomologyPresheaf R n)

/-- Under `homologyIsoCohomologyPresheaf`, the homology class of a cycle `s ∈ Iⁿ(U)` is the class
in `Extⁿ(ℤ_U, F)` of the morphism `ℤ_U ⟶ Iⁿ` corresponding to `s`. -/
lemma homologyIsoCohomologyPresheaf_hom_app_homologyπ_apply (U : C)
    (z : ((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj
      R.cocomplex).cycles n).obj (op U)) :
    F.H'AddEquivExt n U ((R.homologyIsoCohomologyPresheaf n).hom.app (op U)
      (((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj
        R.cocomplex).homologyπ n).app (op U) z)) =
      R.extMk ((freeYonedaSheafSectionsEquiv J U _).symm
        (((((sheafToPresheaf J AddCommGrpCat.{v}).mapHomologicalComplex _).obj
          R.cocomplex).iCycles n).app (op U) z)) (n + 1) rfl
        (R.freeYonedaSheafSectionsEquiv_symm_iCycles_app_comp_d n _ z) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (homologyπ_comp_homologyToCohomologyPresheaf R n) (op U)) z
  rw [NatTrans.comp_app, ConcreteCategory.comp_apply] at h
  rw [← H'AddEquivExt_cyclesToH']
  exact congrArg (F.H'AddEquivExt n U) h

end

end CategoryTheory.InjectiveResolution
