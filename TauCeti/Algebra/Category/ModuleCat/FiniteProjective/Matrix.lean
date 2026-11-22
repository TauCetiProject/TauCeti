/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Basic
public import TauCeti.RingTheory.Morita.Matrix

import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Algebra.Category.ModuleCat.Equivalence

/-!
# Matrix Morita functor on finitely generated projective modules

For a ring `R : Type u` and a finite index type `ι : Type v` with decidable equality, Mathlib's
functor `ModuleCat.toMatrixModCat R ι` (`P ↦ (ι → P)`) preserves finitely generated projective
modules (`TauCeti.finiteProjectiveModules_le_inverseImage_toMatrixModCat`). Lifting it yields a
canonical additive functor `TauCeti.finiteProjectiveModulesToMatrixFunctor R ι` independent of any
choice of index in `ι`, which is an equivalence of categories whenever `ι` is nonempty.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti

variable (R : Type u) [Ring R] (ι : Type v) [Fintype ι] [DecidableEq ι]

/-- `ModuleCat.toMatrixModCat R ι` preserves finitely generated projective modules. -/
theorem finiteProjectiveModules_le_inverseImage_toMatrixModCat :
    finiteProjectiveModules R ≤
      (finiteProjectiveModules (Matrix ι ι R)).inverseImage
        (ModuleCat.toMatrixModCat.{u, v, u} R ι) := by
  intro P hP
  rcases isEmpty_or_nonempty ι with _ | ⟨⟨i⟩⟩
  · have : Subsingleton ((ModuleCat.toMatrixModCat.{u, v, u} R ι).obj P) :=
      subsingleton_of_forall_eq 0 fun _ ↦ funext isEmptyElim
    exact (finiteProjectiveModules _).prop_of_isZero (ModuleCat.isZero_of_subsingleton _)
  · obtain ⟨_, _⟩ := finiteProjectiveModules_iff.mp hP
    have : Small.{max u v} R := small_lift.{u, v} R
    let E := ModuleCat.matrixEquivalence.{u, v, u} R i
    let e := (ULift.moduleEquiv (R := R) (M := P)).symm
    exact (finiteProjectiveModules _).prop_of_iso
        ((toMatrixModCatUliftIso.{u, v, u} R ι).app P).symm <|
      finiteProjectiveModules_iff.mpr
        ⟨(E.finite_functor_obj_iff _).mpr (Module.Finite.equiv e),
         (E.projective_functor_obj_iff _).mpr (Module.Projective.of_equiv e)⟩

/-- Canonical functor sending a finite projective `R`-module `P` to the `Matrix ι ι R`-module
`ι → P`, independent of any choice of index in `ι`. -/
noncomputable def finiteProjectiveModulesToMatrixFunctor :
    (finiteProjectiveModules R).FullSubcategory ⥤
      (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory :=
  (finiteProjectiveModules (Matrix ι ι R)).lift
    ((finiteProjectiveModules R).ι ⋙ ModuleCat.toMatrixModCat.{u, v, u} R ι)
    fun P ↦ finiteProjectiveModules_le_inverseImage_toMatrixModCat R ι P.obj P.property

instance : (finiteProjectiveModulesToMatrixFunctor R ι).Additive :=
  have : (finiteProjectiveModulesToMatrixFunctor R ι ⋙ (finiteProjectiveModules _).ι).Additive :=
    inferInstanceAs ((finiteProjectiveModules R).ι ⋙
      ModuleCat.toMatrixModCat.{u, v, u} R ι).Additive
  Functor.additive_of_comp_faithful _ (finiteProjectiveModules (Matrix ι ι R)).ι

@[simp] theorem finiteProjectiveModulesToMatrixFunctor_obj_obj (P) :
    ((finiteProjectiveModulesToMatrixFunctor R ι).obj P).obj =
      (ModuleCat.toMatrixModCat.{u, v, u} R ι).obj P.obj := (rfl)

@[simp] theorem finiteProjectiveModulesToMatrixFunctor_map_hom {P Q} (g : P ⟶ Q) :
    ((finiteProjectiveModulesToMatrixFunctor R ι).map g).hom =
      eqToHom (finiteProjectiveModulesToMatrixFunctor_obj_obj R ι P) ≫
        (ModuleCat.toMatrixModCat.{u, v, u} R ι).map g.hom ≫
          eqToHom (finiteProjectiveModulesToMatrixFunctor_obj_obj R ι Q).symm :=
  ObjectProperty.lift_map_hom_of_eq rfl g (finiteProjectiveModulesToMatrixFunctor_obj_obj R ι P)
    (finiteProjectiveModulesToMatrixFunctor_obj_obj R ι Q)

variable [Nonempty ι]

/-- For nonempty `ι`, `P ↦ (ι → P)` is an equivalence between finitely generated projective `R`-
and `Matrix ι ι R`-modules. -/
instance : (finiteProjectiveModulesToMatrixFunctor R ι).IsEquivalence := by
  obtain ⟨i⟩ := ‹Nonempty ι›; let E := ModuleCat.matrixEquivalence.{u, v, u} R i
  have : (ModuleCat.toMatrixModCat.{u, v, max u v} R ι).IsEquivalence :=
    inferInstanceAs E.functor.IsEquivalence
  have := Functor.Full.of_iso (toMatrixModCatUliftIso.{u, v, u} R ι).symm
  have := Functor.Faithful.of_iso (toMatrixModCatUliftIso.{u, v, u} R ι).symm
  have : (finiteProjectiveModulesToMatrixFunctor R ι).EssSurj :=
    (ObjectProperty.essSurj_lift_iff _ _ _).mpr fun Q hQ ↦ by
      obtain ⟨hfinQ, hprojQ⟩ := finiteProjectiveModules_iff.mp hQ
      have : Small.{max u v} R := small_lift.{u, v} R
      let M : ModuleCat.{max u v} R := E.inverse.obj Q
      have hfinM : Module.Finite R M := (E.symm.finite_functor_obj_iff Q).mpr hfinQ
      have : Module.Projective R M := (E.symm.projective_functor_obj_iff Q).mpr hprojQ
      have : Small.{u} M := @Module.Finite.small.{u, u, max u v} R M _ _ _ (small_self R) hfinM
      let e := Shrink.linearEquiv.{u} R M; let P₀ : ModuleCat.{u} R := ModuleCat.of R (Shrink.{u} M)
      exact ⟨⟨P₀, finiteProjectiveModules_iff.mpr
        ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩⟩,
        ⟨(toMatrixModCatUliftIso.{u, v, u} R ι).app P₀ ≪≫ E.functor.mapIso
          ((ULift.moduleEquiv (R := R) (M := P₀)).trans e).toModuleIso ≪≫ E.counitIso.app Q⟩⟩
  exact { faithful := ObjectProperty.instFaithfulFullSubcategoryLift _ _ _,
          full := ObjectProperty.instFullFullSubcategoryLift _ _ _ }

end TauCeti
