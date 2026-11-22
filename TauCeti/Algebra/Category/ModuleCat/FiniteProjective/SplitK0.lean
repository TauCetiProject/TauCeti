/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Morita
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Matrix
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.ScalarChange
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent

import TauCeti.Algebra.Group.Prod

/-!
# Split `K₀` of finitely generated projective modules: Morita invariance and products

For a possibly noncommutative ring `R`, this file develops `SplitK0` of
`(finiteProjectiveModules R).FullSubcategory`: ring-isomorphism invariance
(`RingEquiv.finiteProjectiveModulesSplitK0Equiv`), binary product decomposition
(`finiteProjectiveModulesProdSplitK0Equiv`), and canonical universe-polymorphic matrix Morita
invariance (`finiteProjectiveModulesMatrixSplitK0Equiv`).

## References

* C. A. Weibel, *The K-book*, Chapter II, §2, Lemma 2.1, Prop. 2.4, §2.8.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u u' v

/-! ### Ring-isomorphism invariance on `SplitK0` -/

namespace RingEquiv

open TauCeti

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]

/-- A ring isomorphism `e : R ≃+* S` induces an isomorphism on `SplitK0` by extension of scalars. -/
noncomputable def finiteProjectiveModulesSplitK0Equiv (e : R ≃+* S) :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules S).FullSubcategory :=
  AddMonoidHom.toAddEquiv
    (SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} e.symm.toRingHom.finiteProjectiveModulesExtendScalars)
    (AddMonoidHom.ext fun _ ↦ by simp) (AddMonoidHom.ext fun _ ↦ by simp)

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_apply (e : R ≃+* S) (x) :
    e.finiteProjectiveModulesSplitK0Equiv x =
      SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars x := (rfl)

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_symm (e : R ≃+* S) :
    e.finiteProjectiveModulesSplitK0Equiv.symm = e.symm.finiteProjectiveModulesSplitK0Equiv := (rfl)

/-- **Extension and restriction of scalars agree along a ring isomorphism** on `SplitK0`. -/
theorem splitK0Map_finiteProjectiveModulesExtendScalars_eq_restrictScalars (e : R ≃+* S) :
    SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars =
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.finiteProjectiveModulesSplitK0Equiv
        : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+
          SplitK0.{u} (finiteProjectiveModules S).FullSubcategory) :=
  SplitK0.hom_ext fun P ↦ by
    simpa using SplitK0.of_congr.{u} <| ObjectProperty.isoMk _ <|
      eqToIso (e.toRingHom.finiteProjectiveModulesExtendScalars_obj_obj P) ≪≫
        (BalancedExtension.functorRingEquivIso.{u, u, u} e).app P.obj ≪≫
        eqToIso ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          e).symm.finiteProjectiveModulesEquivalence_functor_obj_obj P).symm

theorem finiteProjectiveModulesSplitK0Equiv_eq_restrictScalars (e : R ≃+* S) :
    e.finiteProjectiveModulesSplitK0Equiv =
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.finiteProjectiveModulesSplitK0Equiv :=
  AddEquiv.toAddMonoidHom_injective
    (splitK0Map_finiteProjectiveModulesExtendScalars_eq_restrictScalars e)

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_refl (R : Type u) [Ring R] :
    (RingEquiv.refl R).finiteProjectiveModulesSplitK0Equiv = AddEquiv.refl _ := by ext; simp

theorem finiteProjectiveModulesSplitK0Equiv_trans (e : R ≃+* S) (e' : S ≃+* T) :
    (e.trans e').finiteProjectiveModulesSplitK0Equiv =
      e.finiteProjectiveModulesSplitK0Equiv.trans e'.finiteProjectiveModulesSplitK0Equiv := by
  ext; simp [RingEquiv.toRingHom_trans]

end RingEquiv

namespace TauCeti

/-! ### Binary product rings and matrix rings on `SplitK0` -/

section ProdRing
variable (R S : Type u) [Ring R] [Ring S]

/-- **`SplitK0` of finite projective modules commutes with binary products of rings.** -/
noncomputable def finiteProjectiveModulesProdSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules (R × S)).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ×
        SplitK0.{u} (finiteProjectiveModules S).FullSubcategory :=
  AddEquiv.ofProdCoprod
    (SplitK0.map.{u, u} (RingHom.fst R S).finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} (RingHom.snd R S).finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} ((RingHom.fst R S).finiteProjectiveModulesRestrictScalars
      (RingHom.finite_fst R S) (RingHom.projective_fst R S)))
    (SplitK0.map.{u, u} ((RingHom.snd R S).finiteProjectiveModulesRestrictScalars
      (RingHom.finite_snd R S) (RingHom.projective_snd R S)))
    (SplitK0.hom_ext fun P ↦ by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.prod_apply, AddMonoidHom.coprod_apply,
        SplitK0.map_of, AddMonoidHom.id_apply]
      let e {A : Type u} [Ring A] (p : R × S →+* A) hfin hproj :=
        (((ModuleCat.restrictScalars.{u} p).mapIso
          (eqToIso (p.finiteProjectiveModulesExtendScalars_obj_obj P).symm)) ≪≫ eqToIso
            (p.finiteProjectiveModulesRestrictScalars_obj_obj hfin hproj _).symm).toLinearEquiv
      exact (SplitK0.of_eq_add_of_linearEquiv_prod <|
        (BalancedExtension.prodModuleLinearEquiv R S P.obj).trans <|
          LinearEquiv.prodCongr (e _ _ _) (e _ _ _)).symm)
    (SplitK0.map_extendScalars_comp_restrictScalars_self _ Prod.fst_surjective _ _)
    (SplitK0.map_extendScalars_comp_restrictScalars_eq_zero _ _ _ _ (1, 0) rfl rfl)
    (SplitK0.map_extendScalars_comp_restrictScalars_eq_zero _ _ _ _ (0, 1) rfl rfl)
    (SplitK0.map_extendScalars_comp_restrictScalars_self _ Prod.snd_surjective _ _)

@[simp] theorem finiteProjectiveModulesProdSplitK0Equiv_apply (x) :
    finiteProjectiveModulesProdSplitK0Equiv R S x =
      (SplitK0.map.{u, u} (RingHom.fst R S).finiteProjectiveModulesExtendScalars x,
        SplitK0.map.{u, u} (RingHom.snd R S).finiteProjectiveModulesExtendScalars x) :=
  AddEquiv.ofProdCoprod_apply _ _ _ _ _ _ _ _ _ x

@[simp] theorem finiteProjectiveModulesProdSplitK0Equiv_symm_apply (x) :
    (finiteProjectiveModulesProdSplitK0Equiv R S).symm x =
      SplitK0.map.{u, u} ((RingHom.fst R S).finiteProjectiveModulesRestrictScalars
          (RingHom.finite_fst R S) (RingHom.projective_fst R S)) x.1 +
        SplitK0.map.{u, u} ((RingHom.snd R S).finiteProjectiveModulesRestrictScalars
          (RingHom.finite_snd R S) (RingHom.projective_snd R S)) x.2 :=
  AddEquiv.ofProdCoprod_symm_apply _ _ _ _ _ _ _ _ _ x
end ProdRing

section MatrixMorita
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
end MatrixMorita

end TauCeti
