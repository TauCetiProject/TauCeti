/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Matrix
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.SplitK0.Basic

/-!
# Matrix Morita invariance on split `K₀` of finitely generated projective modules

For a ring `R : Type u` and a nonempty finite index type `ι : Type v` with decidable equality,
`TauCeti.finiteProjectiveModulesMatrixSplitK0Equiv R ι` is the canonical universe-polymorphic
isomorphism `K₀(proj R) ≃+ K₀(proj (Matrix ι ι R))` induced by `P ↦ (ι → P)`, sending `|ι| • [R]`
to `[Matrix ι ι R]` and agreeing with `ModuleCat.matrixEquivalence R i` for every `i : ι`.

## References

* C. A. Weibel, *The K-book*, Chapter II, §2.
-/

public section

open CategoryTheory

universe u v

namespace TauCeti

variable (R : Type u) [Ring R]

section Index
variable (ι : Type v) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- **Matrix Morita invariance of `SplitK0`:** `P ↦ (ι → P)` induces a canonical isomorphism
`K₀(proj R) ≃+ K₀(proj (Matrix ι ι R))`. -/
noncomputable def finiteProjectiveModulesMatrixSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      SplitK0.{max u v} (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory :=
  SplitK0.mapEquiv.{u, max u v} (finiteProjectiveModulesToMatrixFunctor R ι).asEquivalence

theorem finiteProjectiveModulesMatrixSplitK0Equiv_apply (x) :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι x =
      SplitK0.map.{u, max u v} (finiteProjectiveModulesToMatrixFunctor R ι) x :=
  DFunLike.congr_fun (SplitK0.mapEquiv_toAddMonoidHom.{u, max u v} _) x

@[simp] theorem finiteProjectiveModulesMatrixSplitK0Equiv_of (P) :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι (SplitK0.of.{u} P) =
      SplitK0.of.{max u v} ((finiteProjectiveModulesToMatrixFunctor R ι).obj P) :=
  SplitK0.mapEquiv_of.{u, max u v} _ P

/-- Under `finiteProjectiveModulesMatrixSplitK0Equiv`, `|ι| • [R]` maps to `[Matrix ι ι R]`. -/
@[simp] theorem
    finiteProjectiveModulesMatrixSplitK0Equiv_card_nsmul_finiteProjectiveModulesRegular :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι
        (Fintype.card ι • SplitK0.of.{u} (finiteProjectiveModulesRegular R)) =
      SplitK0.of.{max u v} (finiteProjectiveModulesRegular (Matrix ι ι R)) := by
  rw [← SplitK0.of_finFreeObj (R := R) (Fintype.card ι),
    finiteProjectiveModulesMatrixSplitK0Equiv_of]
  let P₀ : ModuleCat.{u} R := ModuleCat.of R (Fin (Fintype.card ι) → R)
  exact SplitK0.of_congr <| ObjectProperty.isoMk _ <|
    eqToIso (finiteProjectiveModulesToMatrixFunctor_obj_obj R ι _) ≪≫
      (ModuleCat.toMatrixModCat.{u, v, u} R ι).mapIso
        (eqToIso (FiniteProjectiveModules.finFreeObj_obj R (Fintype.card ι))) ≪≫
      (toMatrixModCatUliftIso.{u, v, u} R ι).app P₀ ≪≫
      (ModuleCat.toMatrixModCat.{u, v, max u v} R ι).mapIso
        ((ULift.moduleEquiv (R := R) (M := P₀)).trans
          (LinearEquiv.funCongrLeft R R (Fintype.equivFin ι))).toModuleIso ≪≫
      (toMatrixModCatPiLinearEquiv R ι).toModuleIso ≪≫
      eqToIso (finiteProjectiveModulesRegular_obj (Matrix ι ι R)).symm
end Index

/-- For any `i : ι`, `finiteProjectiveModulesToMatrixFunctor` induces the same map on `SplitK0` as
`ModuleCat.matrixEquivalence R i`. -/
theorem map_finiteProjectiveModulesToMatrixFunctor_eq (ι : Type u) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (i : ι) : SplitK0.map.{u, u} (finiteProjectiveModulesToMatrixFunctor R ι) =
      ((ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesSplitK0Equiv :
        SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+
          SplitK0.{u} (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory) :=
  (SplitK0.map_congr.{u, u} fun P ↦ ⟨ObjectProperty.isoMk _ (eqToIso
    ((finiteProjectiveModulesToMatrixFunctor_obj_obj R ι P).trans
      ((ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesEquivalence_functor_obj_obj
        P).symm))⟩).trans (Equivalence.finiteProjectiveModulesSplitK0Equiv_toAddMonoidHom _).symm

/-- For every `i : ι`, `finiteProjectiveModulesMatrixSplitK0Equiv` agrees with the Morita
equivalence induced by `ModuleCat.matrixEquivalence R i`. -/
theorem finiteProjectiveModulesMatrixSplitK0Equiv_eq (ι : Type u) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (i : ι) : finiteProjectiveModulesMatrixSplitK0Equiv R ι =
      (ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesSplitK0Equiv :=
  AddEquiv.toAddMonoidHom_injective <| (SplitK0.mapEquiv_toAddMonoidHom.{u, u} _).trans
    (map_finiteProjectiveModulesToMatrixFunctor_eq R ι i)

end TauCeti
