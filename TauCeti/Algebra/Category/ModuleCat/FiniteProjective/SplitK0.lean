/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.ExtendScalars
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Morita
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.Algebra.Category.ModuleCat.Finrank
public import TauCeti.RingTheory.Morita.Matrix

import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Algebra.Group.Prod
import TauCeti.CategoryTheory.ObjectProperty
import TauCeti.LinearAlgebra.FreeModule.PID
import TauCeti.RingTheory.LocalRing.Module

/-!
# Split `K₀` of finitely generated projective modules: Morita invariance, products, and rank

For a possibly noncommutative ring `R`, this file develops the categorical and group-level API of
`SplitK0 (finiteProjectiveModules R).FullSubcategory`. The right-module specialization
`TauCeti.AlgebraicK0` builds on this file in
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.AlgebraicK0`.

## Main definitions and results

* `TauCeti.SplitK0.of_finiteProjectiveModulesExtendScalars_selfObj`: extension of scalars maps
  the regular module `[R]` to `[S]`.
* `TauCeti.finiteProjectiveModulesSplitK0EquivExactK0`: comparison with `ExactK0`.
* `CategoryTheory.Equivalence.finiteProjectiveModulesSplitK0Equiv`,
  `RingEquiv.finiteProjectiveModulesSplitK0Equiv`, and
  `RingEquiv.map_finiteProjectiveModulesExtendScalars_eq`: Morita and ring-isomorphism invariance,
  and agreement with restriction along `e.symm`.
* `TauCeti.finiteProjectiveModulesProdSplitK0Equiv`: `K₀(proj (R × S)) ≃+ K₀(proj R) × K₀(proj S)`.
* `TauCeti.finiteProjectiveModulesToMatrixFunctor` and
  `TauCeti.finiteProjectiveModulesMatrixSplitK0Equiv`: universe-polymorphic, index-independent
  matrix Morita isomorphism `K₀(proj R) ≃+ K₀(proj M_ι(R))`.
* `TauCeti.finiteProjectiveModulesFinrankSplitK0EquivOfFree` and specializations to division rings,
  principal left-ideal domains, and commutative local rings: the rank isomorphism
  `K₀(proj R) ≃+ ℤ`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2,
  Lemma 2.1, Examples 2.1.1–2.1.2, Proposition 2.4, and §2.8.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u u' v

namespace TauCeti

/-! ### Extension of scalars on the regular module in `SplitK0` -/

namespace SplitK0

/-- Extension of scalars along `f : R →+* S` sends the class of the regular module `R` to the class
of the regular module `S`. -/
@[simp] theorem of_finiteProjectiveModulesExtendScalars_selfObj {R S : Type u} [Ring R] [Ring S]
    (f : R →+* S) :
    SplitK0.of.{u} (f.finiteProjectiveModulesExtendScalars.obj
        (FiniteProjectiveModules.selfObj R)) =
      SplitK0.of.{u} (FiniteProjectiveModules.selfObj S) :=
  of_extendScalars_obj
    ((BalancedExtension.congr f
        ((eqToIso (FiniteProjectiveModules.selfObj_obj R)).toLinearEquiv.trans
          (LinearEquiv.funUnique Unit R R).symm)).trans
      ((BalancedExtension.piScalarRight f Unit).trans
        ((LinearEquiv.funUnique Unit S S).trans
          (eqToIso (FiniteProjectiveModules.selfObj_obj S).symm).toLinearEquiv)))

end SplitK0

/-! ### Comparison between `SplitK0` and `ExactK0` of finitely generated projective modules -/

private theorem split_conflation_finiteProjectiveModules (R : Type u) [Ring R]
    {S : ShortComplex (finiteProjectiveModules R).FullSubcategory}
    (hS : (finiteProjectiveModulesExactStructure R).Conflation S) : Nonempty S.Splitting := by
  rw [finiteProjectiveModulesExactStructure_eq_split] at hS
  exact (ExactStructure.split_conflation S).mp hS

/-- **Comparison between split and exact `K₀` of finitely generated projective modules.** Every
short exact sequence splits (`TauCeti.finiteProjectiveModulesExactStructure_eq_split`), so
`TauCeti.ExactK0.fromSplit` is an isomorphism. -/
noncomputable def finiteProjectiveModulesSplitK0EquivExactK0 (R : Type u) [Ring R] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      ExactK0.{u} (finiteProjectiveModulesExactStructure R) :=
  ExactK0.fromSplitEquiv.{u} (split_conflation_finiteProjectiveModules R)

@[simp] theorem finiteProjectiveModulesSplitK0EquivExactK0_of (R : Type u) [Ring R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesSplitK0EquivExactK0 R (SplitK0.of.{u} P) = ExactK0.of.{u} P :=
  (ExactK0.fromSplitEquiv_apply.{u} (split_conflation_finiteProjectiveModules R)
    (SplitK0.of.{u} P)).trans (ExactK0.fromSplit_of.{u} P)

@[simp] theorem finiteProjectiveModulesSplitK0EquivExactK0_symm_of (R : Type u) [Ring R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    (finiteProjectiveModulesSplitK0EquivExactK0 R).symm (ExactK0.of.{u} P) = SplitK0.of.{u} P :=
  ExactK0.fromSplitEquiv_symm_of.{u} (split_conflation_finiteProjectiveModules R) P

/-- `TauCeti.finiteProjectiveModulesSplitK0EquivExactK0` intertwines extension of scalars on
`SplitK0` and `ExactK0`. -/
theorem finiteProjectiveModulesSplitK0EquivExactK0_comp_map_extendScalars {R S : Type u} [Ring R]
    [Ring S] (f : R →+* S) :
    (finiteProjectiveModulesSplitK0EquivExactK0 S).toAddMonoidHom.comp
        (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars) =
      f.finiteProjectiveModulesK0Extend.comp
        (finiteProjectiveModulesSplitK0EquivExactK0 R).toAddMonoidHom :=
  SplitK0.hom_ext fun _ ↦ by simp

@[simp] theorem finiteProjectiveModulesSplitK0EquivExactK0_map_extendScalars {R S : Type u} [Ring R]
    [Ring S] (f : R →+* S) (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesSplitK0EquivExactK0 S
        (SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars x) =
      f.finiteProjectiveModulesK0Extend (finiteProjectiveModulesSplitK0EquivExactK0 R x) :=
  DFunLike.congr_fun (finiteProjectiveModulesSplitK0EquivExactK0_comp_map_extendScalars f) x

end TauCeti

/-! ### Morita invariance and ring-isomorphism invariance on `SplitK0` -/

namespace CategoryTheory.Equivalence

open TauCeti

variable {A : Type u} [Ring A] {B : Type u'} [Ring B] (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B)

/-- **Morita invariance of `SplitK0` of finitely generated projective modules.** An equivalence
`e : ModuleCat A ≌ ModuleCat B` induces an isomorphism on `SplitK0` of finitely generated
projective modules. -/
noncomputable def finiteProjectiveModulesSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules A).FullSubcategory ≃+
      SplitK0.{u'} (finiteProjectiveModules B).FullSubcategory :=
  SplitK0.mapEquiv.{u, u'} e.finiteProjectiveModulesEquivalence

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_of
    (P : (finiteProjectiveModules A).FullSubcategory) :
    e.finiteProjectiveModulesSplitK0Equiv (SplitK0.of.{u} P) =
      SplitK0.of.{u'} (e.finiteProjectiveModulesEquivalence.functor.obj P) :=
  SplitK0.mapEquiv_of.{u, u'} _ P

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_symm_of
    (Q : (finiteProjectiveModules B).FullSubcategory) :
    e.finiteProjectiveModulesSplitK0Equiv.symm (SplitK0.of.{u'} Q) =
      SplitK0.of.{u} (e.finiteProjectiveModulesEquivalence.inverse.obj Q) :=
  SplitK0.mapEquiv_symm_of.{u, u'} _ Q

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_toAddMonoidHom :
    (e.finiteProjectiveModulesSplitK0Equiv :
        SplitK0.{u} (finiteProjectiveModules A).FullSubcategory →+
          SplitK0.{u'} (finiteProjectiveModules B).FullSubcategory) =
      SplitK0.map.{u, u'} e.finiteProjectiveModulesEquivalence.functor :=
  SplitK0.mapEquiv_toAddMonoidHom.{u, u'} _

/-- `TauCeti.finiteProjectiveModulesSplitK0EquivExactK0` intertwines Morita equivalences on
`SplitK0` and on `ExactK0`. -/
@[simp] theorem finiteProjectiveModulesSplitK0EquivExactK0_finiteProjectiveModulesSplitK0Equiv
    (x : SplitK0.{u} (finiteProjectiveModules A).FullSubcategory) :
    TauCeti.finiteProjectiveModulesSplitK0EquivExactK0 B (e.finiteProjectiveModulesSplitK0Equiv x) =
      e.finiteProjectiveModulesK0Equiv (TauCeti.finiteProjectiveModulesSplitK0EquivExactK0 A x) :=
  DFunLike.congr_fun (SplitK0.hom_ext
    (f := (TauCeti.finiteProjectiveModulesSplitK0EquivExactK0 B).toAddMonoidHom.comp
      e.finiteProjectiveModulesSplitK0Equiv.toAddMonoidHom)
    (g := e.finiteProjectiveModulesK0Equiv.toAddMonoidHom.comp
      (TauCeti.finiteProjectiveModulesSplitK0EquivExactK0 A).toAddMonoidHom) fun _ ↦ by simp) x

end CategoryTheory.Equivalence

namespace RingEquiv

open TauCeti

section Basic

variable {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)

/-- A ring isomorphism `e : R ≃+* S` induces an isomorphism on `SplitK0` of finitely generated
projective modules by extension of scalars along `e` and `e.symm`. -/
noncomputable def finiteProjectiveModulesSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules S).FullSubcategory :=
  AddMonoidHom.toAddEquiv
    (SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} e.symm.toRingHom.finiteProjectiveModulesExtendScalars)
    (AddMonoidHom.ext fun x ↦ by simp) (AddMonoidHom.ext fun x ↦ by simp)

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_apply
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    e.finiteProjectiveModulesSplitK0Equiv x =
      SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars x := (rfl)

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_symm :
    e.finiteProjectiveModulesSplitK0Equiv.symm = e.symm.finiteProjectiveModulesSplitK0Equiv := (rfl)

/-- **Extension and restriction of scalars agree along a ring isomorphism.** For `e : R ≃+* S`,
extension of scalars along `e.toRingHom` induces the same map on `SplitK0` as restriction of scalars
along `e.symm` (`(ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm`). -/
theorem map_finiteProjectiveModulesExtendScalars_eq :
    SplitK0.map.{u, u} e.toRingHom.finiteProjectiveModulesExtendScalars =
      ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          e).symm.finiteProjectiveModulesSplitK0Equiv :
        SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+
          SplitK0.{u} (finiteProjectiveModules S).FullSubcategory) := by
  refine SplitK0.hom_ext fun P ↦ ?_
  rw [SplitK0.map_of, Equivalence.finiteProjectiveModulesSplitK0Equiv_toAddMonoidHom,
    SplitK0.map_of]
  exact SplitK0.of_congr <| ObjectProperty.isoMk _ <|
    eqToIso (e.toRingHom.finiteProjectiveModulesExtendScalars_obj_obj P) ≪≫
      (BalancedExtension.functorRingEquivIso.{u, u, u} e).app P.obj ≪≫
      eqToIso ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        e).symm.finiteProjectiveModulesEquivalence_functor_obj_obj P).symm

theorem finiteProjectiveModulesSplitK0Equiv_eq_restrictScalars :
    e.finiteProjectiveModulesSplitK0Equiv =
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        e).symm.finiteProjectiveModulesSplitK0Equiv :=
  AddEquiv.toAddMonoidHom_injective (map_finiteProjectiveModulesExtendScalars_eq e)

end Basic

@[simp] theorem finiteProjectiveModulesSplitK0Equiv_refl (R : Type u) [Ring R] :
    (RingEquiv.refl R).finiteProjectiveModulesSplitK0Equiv = AddEquiv.refl _ := by ext x; simp

theorem finiteProjectiveModulesSplitK0Equiv_trans {R S T : Type u} [Ring R] [Ring S] [Ring T]
    (e : R ≃+* S) (e' : S ≃+* T) :
    (e.trans e').finiteProjectiveModulesSplitK0Equiv =
      e.finiteProjectiveModulesSplitK0Equiv.trans e'.finiteProjectiveModulesSplitK0Equiv := by
  ext x; simp [RingEquiv.toRingHom_trans]

end RingEquiv

namespace TauCeti

/-! ### Zero ring, binary product rings, matrix rings, and rank isomorphisms on `SplitK0` -/

/-- Over a subsingleton (zero) ring, every module is a zero object, so `SplitK0` of finitely
generated projective modules is trivial. -/
instance {R : Type u} [Ring R] [Subsingleton R] :
    Subsingleton (SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :=
  subsingleton_of_forall_eq 0 <| DFunLike.congr_fun <|
    SplitK0.hom_ext (f := AddMonoidHom.id _) (g := 0) fun P ↦ by
      have : Subsingleton P.obj := Module.subsingleton R P.obj
      exact SplitK0.of_eq_zero_of_isZero (IsZero.of_full_of_faithful_of_isZero
        (finiteProjectiveModules R).ι P (ModuleCat.isZero_of_subsingleton P.obj))

section ProdRing

private theorem of_extendScalars_splitRestrict_eq_zero {E A B : Type u} [Ring E] [Ring A] [Ring B]
    (p : E →+* A) (p' : E →+* B)
    (hfin : letI := p'.toModule; Module.Finite E B)
    (hproj : letI := p'.toModule; Module.Projective E B)
    (e : E) (hp : p e = 1) (hp' : p' e = 0) (N : (finiteProjectiveModules B).FullSubcategory) :
    SplitK0.of.{u}
        (p.finiteProjectiveModulesExtendScalars.obj
          ((p'.finiteProjectiveModulesRestrictScalars hfin hproj).obj N)) = 0 := by
  let Z : ModuleCat.{u} A :=
    ModuleCat.of A (BalancedExtension p ((ModuleCat.restrictScalars.{u} p').obj N.obj))
  have : Subsingleton Z :=
    BalancedExtension.subsingleton_restrictScalars_of_map_eq_one_of_map_eq_zero p p' e hp hp' N.obj
  have hZ : (p.finiteProjectiveModulesExtendScalars.obj
      ((p'.finiteProjectiveModulesRestrictScalars hfin hproj).obj N)).obj = Z := by
    rw [p.finiteProjectiveModulesExtendScalars_obj_obj,
      p'.finiteProjectiveModulesRestrictScalars_obj_obj]
  exact SplitK0.of_eq_zero_of_isZero <| IsZero.of_full_of_faithful_of_isZero
    (finiteProjectiveModules A).ι _ <| (ModuleCat.isZero_of_subsingleton Z).of_iso (eqToIso hZ)

variable (R S : Type u) [Ring R] [Ring S]

/-- **`SplitK0` of finitely generated projective modules commutes with binary products of rings.**
The forward map applies extension of scalars along `RingHom.fst R S` and `RingHom.snd R S`, and the
inverse adds restriction of scalars along the two projections. -/
noncomputable def finiteProjectiveModulesProdSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules (R × S)).FullSubcategory ≃+
      SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ×
        SplitK0.{u} (finiteProjectiveModules S).FullSubcategory :=
  AddEquiv.ofProdCoprod
    (SplitK0.map.{u, u} (RingHom.fst R S).finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} (RingHom.snd R S).finiteProjectiveModulesExtendScalars)
    (SplitK0.map.{u, u} ((RingHom.fst R S).finiteProjectiveModulesRestrictScalars
      (RingHom.finite_toModule_of_surjective _ Prod.fst_surjective)
      (RingHom.projective_toModule_of_split _ (AddMonoidHom.inl R S) (by simp)
        AddMonoidHom.mul_inl)))
    (SplitK0.map.{u, u} ((RingHom.snd R S).finiteProjectiveModulesRestrictScalars
      (RingHom.finite_toModule_of_surjective _ Prod.snd_surjective)
      (RingHom.projective_toModule_of_split _ (AddMonoidHom.inr R S) (by simp)
        AddMonoidHom.mul_inr)))
    (SplitK0.hom_ext fun P ↦ by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.prod_apply, AddMonoidHom.coprod_apply,
        SplitK0.map_of, AddMonoidHom.id_apply]
      exact (SplitK0.of_eq_add_of_linearEquiv_prod
        ((BalancedExtension.prodModuleLinearEquiv R S P.obj).trans <| LinearEquiv.prodCongr
          (((ModuleCat.restrictScalars.{u} (RingHom.fst R S)).mapIso
            (eqToIso ((RingHom.fst R S).finiteProjectiveModulesExtendScalars_obj_obj P).symm)) ≪≫
            eqToIso ((RingHom.fst R S).finiteProjectiveModulesRestrictScalars_obj_obj
              _ _ _).symm).toLinearEquiv
          (((ModuleCat.restrictScalars.{u} (RingHom.snd R S)).mapIso
            (eqToIso ((RingHom.snd R S).finiteProjectiveModulesExtendScalars_obj_obj P).symm)) ≪≫
            eqToIso ((RingHom.snd R S).finiteProjectiveModulesRestrictScalars_obj_obj
              _ _ _).symm).toLinearEquiv)).symm)
    (SplitK0.hom_ext fun M ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.id_apply]
      exact SplitK0.of_extendScalars_obj
        ((BalancedExtension.congr (RingHom.fst R S)
            (eqToIso ((RingHom.fst R S).finiteProjectiveModulesRestrictScalars_obj_obj
              _ _ M)).toLinearEquiv).trans
          (BalancedExtension.restrictScalarsSelfEquiv (RingHom.fst R S) Prod.fst_surjective M.obj)))
    (SplitK0.hom_ext fun N ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.zero_apply]
      exact of_extendScalars_splitRestrict_eq_zero (RingHom.fst R S) (RingHom.snd R S)
        _ _ (1, 0) rfl rfl N)
    (SplitK0.hom_ext fun M ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.zero_apply]
      exact of_extendScalars_splitRestrict_eq_zero (RingHom.snd R S) (RingHom.fst R S)
        _ _ (0, 1) rfl rfl M)
    (SplitK0.hom_ext fun N ↦ by
      simp only [AddMonoidHom.comp_apply, SplitK0.map_of, AddMonoidHom.id_apply]
      exact SplitK0.of_extendScalars_obj
        ((BalancedExtension.congr (RingHom.snd R S)
            (eqToIso ((RingHom.snd R S).finiteProjectiveModulesRestrictScalars_obj_obj
              _ _ N)).toLinearEquiv).trans
          (BalancedExtension.restrictScalarsSelfEquiv (RingHom.snd R S) Prod.snd_surjective N.obj)))

@[simp] theorem finiteProjectiveModulesProdSplitK0Equiv_apply
    (x : SplitK0.{u} (finiteProjectiveModules (R × S)).FullSubcategory) :
    finiteProjectiveModulesProdSplitK0Equiv R S x =
      (SplitK0.map.{u, u} (RingHom.fst R S).finiteProjectiveModulesExtendScalars x,
        SplitK0.map.{u, u} (RingHom.snd R S).finiteProjectiveModulesExtendScalars x) :=
  AddEquiv.ofProdCoprod_apply _ _ _ _ _ _ _ _ _ x

@[simp] theorem finiteProjectiveModulesProdSplitK0Equiv_symm_apply
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ×
      SplitK0.{u} (finiteProjectiveModules S).FullSubcategory) :
    (finiteProjectiveModulesProdSplitK0Equiv R S).symm x =
      SplitK0.map.{u, u} ((RingHom.fst R S).finiteProjectiveModulesRestrictScalars
          (RingHom.finite_toModule_of_surjective _ Prod.fst_surjective)
          (RingHom.projective_toModule_of_split _ (AddMonoidHom.inl R S) (by simp)
            AddMonoidHom.mul_inl)) x.1 +
        SplitK0.map.{u, u} ((RingHom.snd R S).finiteProjectiveModulesRestrictScalars
          (RingHom.finite_toModule_of_surjective _ Prod.snd_surjective)
          (RingHom.projective_toModule_of_split _ (AddMonoidHom.inr R S) (by simp)
            AddMonoidHom.mul_inr)) x.2 :=
  AddEquiv.ofProdCoprod_symm_apply _ _ _ _ _ _ _ _ _ x

end ProdRing

section MatrixMorita

variable (R : Type u) [Ring R]

section Index

variable (ι : Type v) [Fintype ι] [DecidableEq ι]

private def toMatrixModCatUliftIso :
    ModuleCat.toMatrixModCat.{u, v, u} R ι ≅
      ModuleCat.uliftFunctor.{v, u, u} R ⋙ ModuleCat.toMatrixModCat.{u, v, max u v} R ι :=
  NatIso.ofComponents (fun M ↦
    ({ toFun := fun f i ↦ ULift.up (f i)
       invFun := fun f i ↦ (f i).down
       left_inv := fun _ ↦ rfl
       right_inv := fun _ ↦ rfl
       map_add' := fun _ _ ↦ rfl
       map_smul' := fun A w ↦ funext fun i ↦ ULift.ext <| by
         dsimp only
         rw [ModuleCat.toMatrixModCat_obj_smul_apply]
         exact (map_sum (ULift.moduleEquiv (R := R) (M := M))
           (fun j ↦ A i j • ULift.up (w j)) Finset.univ).symm } :
      ((ModuleCat.toMatrixModCat.{u, v, u} R ι).obj M) ≃ₗ[Matrix ι ι R]
        ((ModuleCat.toMatrixModCat.{u, v, max u v} R ι).obj
          ((ModuleCat.uliftFunctor.{v, u, u} R).obj M))).toModuleIso)
    fun _ ↦ ModuleCat.hom_ext <| LinearMap.ext fun _ ↦ funext fun _ ↦ rfl

private theorem finiteProjectiveModules_toMatrixModCat
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModules (Matrix ι ι R)
      ((ModuleCat.toMatrixModCat.{u, v, u} R ι).obj P.obj) := by
  rcases isEmpty_or_nonempty ι with _ | ⟨⟨i⟩⟩
  · have : Subsingleton ((ModuleCat.toMatrixModCat.{u, v, u} R ι).obj P.obj) :=
      subsingleton_of_forall_eq 0 fun _ ↦ funext fun i ↦ isEmptyElim i
    exact (finiteProjectiveModules (Matrix ι ι R)).prop_of_isZero
      (ModuleCat.isZero_of_subsingleton _)
  · obtain ⟨hfinP, hprojP⟩ := finiteProjectiveModules_iff.mp P.property
    have : Small.{max u v} R := small_lift.{u, v} R
    let U : ModuleCat.{max u v} R := (ModuleCat.uliftFunctor.{v, u, u} R).obj P.obj
    have hfinU : Module.Finite R U :=
      Module.Finite.equiv (ULift.moduleEquiv (R := R) (M := P.obj)).symm
    have hprojU : Module.Projective R U :=
      Module.Projective.of_equiv (ULift.moduleEquiv (R := R) (M := P.obj)).symm
    let E := ModuleCat.matrixEquivalence.{u, v, u} R i
    have hfinM : Module.Finite (Matrix ι ι R) (E.functor.obj U) :=
      (E.finite_functor_obj_iff U).mpr hfinU
    have hprojM : Module.Projective (Matrix ι ι R) (E.functor.obj U) :=
      (E.projective_functor_obj_iff U).mpr hprojU
    exact (finiteProjectiveModules (Matrix ι ι R)).prop_of_iso
      ((toMatrixModCatUliftIso R ι).app P.obj).symm
      (finiteProjectiveModules_iff.mpr ⟨hfinM, hprojM⟩)

/-- The canonical functor sending a finitely generated projective `R`-module `P` to the finitely
generated projective `Matrix ι ι R`-module `ι → P`, manifestly independent of any choice of index
in `ι`. -/
noncomputable def finiteProjectiveModulesToMatrixFunctor :
    (finiteProjectiveModules R).FullSubcategory ⥤
      (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory :=
  (finiteProjectiveModules (Matrix ι ι R)).lift
    ((finiteProjectiveModules R).ι ⋙ ModuleCat.toMatrixModCat.{u, v, u} R ι)
    (finiteProjectiveModules_toMatrixModCat R ι)

instance : (finiteProjectiveModulesToMatrixFunctor R ι).Additive := by
  have : (finiteProjectiveModulesToMatrixFunctor R ι ⋙
      (finiteProjectiveModules (Matrix ι ι R)).ι).Additive :=
    inferInstanceAs ((finiteProjectiveModules R).ι ⋙
      ModuleCat.toMatrixModCat.{u, v, u} R ι).Additive
  exact Functor.additive_of_comp_faithful _ (finiteProjectiveModules (Matrix ι ι R)).ι

@[simp] theorem finiteProjectiveModulesToMatrixFunctor_obj_obj
    (P : (finiteProjectiveModules R).FullSubcategory) :
    ((finiteProjectiveModulesToMatrixFunctor R ι).obj P).obj =
      (ModuleCat.toMatrixModCat.{u, v, u} R ι).obj P.obj := (rfl)

@[simp] theorem finiteProjectiveModulesToMatrixFunctor_map_hom
    {P Q : (finiteProjectiveModules R).FullSubcategory} (g : P ⟶ Q) :
    ((finiteProjectiveModulesToMatrixFunctor R ι).map g).hom =
      eqToHom (finiteProjectiveModulesToMatrixFunctor_obj_obj R ι P) ≫
        (ModuleCat.toMatrixModCat.{u, v, u} R ι).map g.hom ≫
          eqToHom (finiteProjectiveModulesToMatrixFunctor_obj_obj R ι Q).symm :=
  ObjectProperty.lift_map_hom_of_eq rfl g
    (finiteProjectiveModulesToMatrixFunctor_obj_obj R ι P)
    (finiteProjectiveModulesToMatrixFunctor_obj_obj R ι Q)

variable [Nonempty ι]

instance : (finiteProjectiveModulesToMatrixFunctor R ι).IsEquivalence := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  let E := ModuleCat.matrixEquivalence.{u, v, u} R i
  have : (ModuleCat.toMatrixModCat.{u, v, max u v} R ι).IsEquivalence :=
    inferInstanceAs E.functor.IsEquivalence
  have : (ModuleCat.toMatrixModCat.{u, v, u} R ι).Full :=
    Functor.Full.of_iso (toMatrixModCatUliftIso R ι).symm
  have : (ModuleCat.toMatrixModCat.{u, v, u} R ι).Faithful :=
    Functor.Faithful.of_iso (toMatrixModCatUliftIso R ι).symm
  have : (finiteProjectiveModulesToMatrixFunctor R ι).Full := by
    unfold finiteProjectiveModulesToMatrixFunctor; infer_instance
  have : (finiteProjectiveModulesToMatrixFunctor R ι).Faithful := by
    unfold finiteProjectiveModulesToMatrixFunctor; infer_instance
  have : (finiteProjectiveModulesToMatrixFunctor R ι).EssSurj := by
    rw [finiteProjectiveModulesToMatrixFunctor, ObjectProperty.essSurj_lift_iff]
    intro Q hQ
    obtain ⟨hfinQ, hprojQ⟩ := finiteProjectiveModules_iff.mp hQ
    have : Small.{max u v} R := small_lift.{u, v} R
    let M : ModuleCat.{max u v} R := E.inverse.obj Q
    have hfinM : Module.Finite R M := (E.symm.finite_functor_obj_iff Q).mpr hfinQ
    have hprojM : Module.Projective R M := (E.symm.projective_functor_obj_iff Q).mpr hprojQ
    have : Small.{u} M := @Module.Finite.small.{u, u, max u v} R M _ _ _ (small_self R) hfinM
    let e : Shrink.{u} M ≃ₗ[R] M := Shrink.linearEquiv R M
    let P₀ : ModuleCat.{u} R := ModuleCat.of R (Shrink.{u} M)
    have hfinP : Module.Finite R P₀ := Module.Finite.equiv e.symm
    have hprojP : Module.Projective R P₀ := Module.Projective.of_equiv e.symm
    refine ⟨⟨P₀, finiteProjectiveModules_iff.mpr ⟨hfinP, hprojP⟩⟩, ⟨?_⟩⟩
    exact (toMatrixModCatUliftIso R ι).app P₀ ≪≫
      E.functor.mapIso ((ULift.moduleEquiv (R := R) (M := P₀)).trans e).toModuleIso ≪≫
      E.counitIso.app Q
  exact {}

/-- **Matrix Morita invariance of `SplitK0`.** Sending `P` to the column module `ι → P` induces an
isomorphism `SplitK0 (finiteProjectiveModules R).FullSubcategory ≃+
SplitK0 (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory` whose underlying map is
independent of any choice of index in `ι`. -/
noncomputable def finiteProjectiveModulesMatrixSplitK0Equiv :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+
      SplitK0.{max u v} (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory :=
  SplitK0.mapEquiv.{u, max u v} (finiteProjectiveModulesToMatrixFunctor R ι).asEquivalence

theorem finiteProjectiveModulesMatrixSplitK0Equiv_apply
    (x : SplitK0.{u} (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι x =
      SplitK0.map.{u, max u v} (finiteProjectiveModulesToMatrixFunctor R ι) x :=
  DFunLike.congr_fun (SplitK0.mapEquiv_toAddMonoidHom.{u, max u v}
    (finiteProjectiveModulesToMatrixFunctor R ι).asEquivalence) x

@[simp] theorem finiteProjectiveModulesMatrixSplitK0Equiv_of
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι (SplitK0.of.{u} P) =
      SplitK0.of.{max u v} ((finiteProjectiveModulesToMatrixFunctor R ι).obj P) :=
  SplitK0.mapEquiv_of.{u, max u v} _ P

/-- Under `TauCeti.finiteProjectiveModulesMatrixSplitK0Equiv`, `|ι|` copies of `[R]` map to the
class of the regular module `[Matrix ι ι R]`. -/
@[simp] theorem finiteProjectiveModulesMatrixSplitK0Equiv_card_nsmul_selfObj :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι
        (Fintype.card ι • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R)) =
      SplitK0.of.{max u v} (FiniteProjectiveModules.selfObj (Matrix ι ι R)) := by
  rw [← SplitK0.of_finFreeObj (R := R) (Fintype.card ι),
    finiteProjectiveModulesMatrixSplitK0Equiv_of]
  let P₀ : ModuleCat.{u} R := ModuleCat.of R (Fin (Fintype.card ι) → R)
  exact SplitK0.of_congr <| ObjectProperty.isoMk _ <|
    eqToIso (finiteProjectiveModulesToMatrixFunctor_obj_obj R ι _) ≪≫
      (ModuleCat.toMatrixModCat.{u, v, u} R ι).mapIso
        (eqToIso (FiniteProjectiveModules.finFreeObj_obj R (Fintype.card ι))) ≪≫
      (toMatrixModCatUliftIso R ι).app P₀ ≪≫
      (ModuleCat.toMatrixModCat.{u, v, max u v} R ι).mapIso
        ((ULift.moduleEquiv (R := R) (M := P₀)).trans
          (LinearEquiv.funCongrLeft R R (Fintype.equivFin ι))).toModuleIso ≪≫
      (toMatrixModCatPiLinearEquiv R ι).toModuleIso ≪≫
      eqToIso (FiniteProjectiveModules.selfObj_obj (Matrix ι ι R)).symm

end Index

section SameUniverse

variable (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- For any index `i : ι`, `TauCeti.finiteProjectiveModulesToMatrixFunctor` induces the same map on
`SplitK0` as `ModuleCat.matrixEquivalence R i`. -/
theorem map_finiteProjectiveModulesToMatrixFunctor_eq (i : ι) :
    SplitK0.map.{u, u} (finiteProjectiveModulesToMatrixFunctor R ι) =
      ((ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesSplitK0Equiv :
        SplitK0.{u} (finiteProjectiveModules R).FullSubcategory →+
          SplitK0.{u} (finiteProjectiveModules (Matrix ι ι R)).FullSubcategory) := by
  rw [Equivalence.finiteProjectiveModulesSplitK0Equiv_toAddMonoidHom]
  exact SplitK0.map_congr.{u, u} fun P ↦ ⟨ObjectProperty.isoMk _ (eqToIso
    ((finiteProjectiveModulesToMatrixFunctor_obj_obj R ι P).trans
      ((ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesEquivalence_functor_obj_obj
        P).symm))⟩

/-- For every `i : ι`, `TauCeti.finiteProjectiveModulesMatrixSplitK0Equiv` agrees with the
Morita equivalence induced by `ModuleCat.matrixEquivalence R i`. -/
theorem finiteProjectiveModulesMatrixSplitK0Equiv_eq (i : ι) :
    finiteProjectiveModulesMatrixSplitK0Equiv R ι =
      (ModuleCat.matrixEquivalence R (ι := ι) i).finiteProjectiveModulesSplitK0Equiv :=
  AddEquiv.toAddMonoidHom_injective <|
    (SplitK0.mapEquiv_toAddMonoidHom.{u, u} _).trans
      (map_finiteProjectiveModulesToMatrixFunctor_eq R ι i)

end SameUniverse

end MatrixMorita

section Finrank

section OfFree

variable (R : Type u) [Ring R] [StrongRankCondition R]

@[simp] theorem FiniteProjectiveModules.finrank_selfObj :
    Module.finrank R (FiniteProjectiveModules.selfObj R).obj = 1 := by
  rw [FiniteProjectiveModules.selfObj_obj]
  exact ModuleCat.finrank_of_self R

variable (hfree : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.Free R P.obj)

private noncomputable def finrankSplitK0Invariant :
    SplitK0.AdditiveInvariant (finiteProjectiveModules R).FullSubcategory ℤ where
  obj P := (Module.finrank R P.obj : ℤ)
  map_iso P Q e :=
    congrArg Nat.cast (((finiteProjectiveModules R).ι.mapIso e).toLinearEquiv.finrank_eq)
  map_biprod P Q := by
    have := hfree P; have := hfree Q
    exact_mod_cast (FiniteProjectiveModules.biprodLinearEquiv P Q).finrank_eq.trans
      Module.finrank_prod

/-- **Rank isomorphism `K₀(proj R) ≃+ ℤ` when finitely generated projective modules are free.**
Over a ring `R` satisfying `StrongRankCondition R` in which every finitely generated projective
left `R`-module is free, `Module.finrank` descends to an isomorphism sending `[P]` to `finrank R P`
and `[R]` to `1`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivOfFree :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+ ℤ :=
  AddMonoidHom.toAddEquiv
    (SplitK0.lift.{u} (finrankSplitK0Invariant R hfree))
    (zmultiplesHom (SplitK0.{u} (finiteProjectiveModules R).FullSubcategory)
      (SplitK0.of.{u} (FiniteProjectiveModules.selfObj R)))
    (SplitK0.hom_ext fun P ↦ by
      have := hfree P
      simp only [AddMonoidHom.comp_apply, SplitK0.lift_of, finrankSplitK0Invariant,
        zmultiplesHom_apply, natCast_zsmul, AddMonoidHom.id_apply]
      exact (SplitK0.of_eq_nsmul_of_linearEquiv_fin (X := P)
        (R' := FiniteProjectiveModules.selfObj R)
        (Module.finBasis R P.obj).equivFun
        (eqToIso (FiniteProjectiveModules.selfObj_obj R)).toLinearEquiv).symm)
    (AddMonoidHom.ext_int <| by simp [finrankSplitK0Invariant])

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivOfFree_of
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesFinrankSplitK0EquivOfFree R hfree (SplitK0.of.{u} P) =
      (Module.finrank R P.obj : ℤ) :=
  SplitK0.lift_of.{u} _ P

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivOfFree_symm_apply (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivOfFree R hfree).symm n =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) := (rfl)

end OfFree

/-- Over a division ring `D`, `Module.finrank` induces `K₀(proj D) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivDivisionRing (D : Type u)
    [DivisionRing D] : SplitK0.{u} (finiteProjectiveModules D).FullSubcategory ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree D fun _ ↦ inferInstance

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_of (D : Type u)
    [DivisionRing D] (P : (finiteProjectiveModules D).FullSubcategory) :
    finiteProjectiveModulesFinrankSplitK0EquivDivisionRing D (SplitK0.of.{u} P) =
      (Module.finrank D P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree_of D _ P

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivDivisionRing_symm_apply (D : Type u)
    [DivisionRing D] (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivDivisionRing D).symm n =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj D) := (rfl)

section PID

variable (R : Type u) [Ring R] [Nontrivial R] [NoZeroDivisors R] [IsPrincipalIdealRing R]

/-- Over a nontrivial principal left-ideal ring without zero divisors, `Module.finrank` induces
`K₀(proj R) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivPID :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree R fun P ↦
    Module.Free.of_injective_of_projective_of_isPrincipalIdealRing
      (LinearMap.id : P.obj →ₗ[R] P.obj) Function.injective_id

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivPID_of
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesFinrankSplitK0EquivPID R (SplitK0.of.{u} P) =
      (Module.finrank R P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree_of R _ P

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivPID_symm_apply (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivPID R).symm n =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) := (rfl)

end PID

section LocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- Over a commutative local ring `R`, `Module.finrank` induces `K₀(proj R) ≃+ ℤ`. -/
noncomputable def finiteProjectiveModulesFinrankSplitK0EquivLocalRing :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+ ℤ :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree R fun _ ↦
    Module.free_of_projective_of_isLocalRing

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivLocalRing_of
    (P : (finiteProjectiveModules R).FullSubcategory) :
    finiteProjectiveModulesFinrankSplitK0EquivLocalRing R (SplitK0.of.{u} P) =
      (Module.finrank R P.obj : ℤ) :=
  finiteProjectiveModulesFinrankSplitK0EquivOfFree_of R _ P

@[simp] theorem finiteProjectiveModulesFinrankSplitK0EquivLocalRing_symm_apply (n : ℤ) :
    (finiteProjectiveModulesFinrankSplitK0EquivLocalRing R).symm n =
      n • SplitK0.of.{u} (FiniteProjectiveModules.selfObj R) := (rfl)

end LocalRing

end Finrank

end TauCeti
