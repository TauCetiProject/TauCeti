/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Affine.Basic

/-!
# Restriction-of-scalars comparison for global sections on an affine formal completion

For a finitely generated ideal `J` of a commutative ring `R` with `R ⧸ J` Noetherian, the inverse
functor of `coherentFormalModuleEquivSpecOfFG J fg` takes global sections over the completed ring
`AdicCompletion J R`. This file constructs the natural isomorphism
`coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso` identifying the underlying
`R`-module (via `ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))`) with
`specSectionsLim J`, together with the explicit formulas on level-`n` limit projections.

## Main definitions

* `coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso`:
  natural isomorphism between the restricted-scalars inverse of `coherentFormalModuleEquivSpecOfFG`
  and `specSectionsLim J`.

## Main results

* `coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso_inv_app_limπ`
* `coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso_hom_app_limπ`
-/

public section

open CategoryTheory Opposite AlgebraicGeometry
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

universe u

namespace AlgebraicGeometry.Scheme.formalCompletion

noncomputable section

variable {R : Type u} [CommRing R]

private lemma completionIso_hom_app (J : Ideal R) (fg : J.FG) (n : ℕ) :
    (Spf.completionIso J fg).hom.app n =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((AdicRing.completion J fg).ideal ^ (n + 1))
        (algebraMap R (AdicCompletion J R))
        ((Ideal.pow_right_mono Ideal.le_comap_map (n + 1)).trans
          (Ideal.le_comap_pow _ (n + 1))))) := by
  rw [Spf.completionIso_hom, AdicThickeningSystem.spfMap_app]

private def pullbackCompletionIso (J : Ideal R) (fg : J.FG) :
    CoherentFormalModule.pullback (specIso J).inv ⋙
        CoherentFormalModule.pullback (Spf.completionIso J fg).hom ≅
      CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv :=
  CoherentFormalModule.pullbackComp (Spf.completionIso J fg).hom (specIso J).inv ≪≫
    CoherentFormalModule.pullbackCongr (specIsoSpfCompletion_inv J fg).symm

private def specSectionsTowerCompletionLevelHom (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) (n : ℕ) :
    ((specSectionsTower J).obj M).obj (op n) ⟶
      (ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))).obj
        (((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
          ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).obj (op n)) :=
  let φ := algebraMap R (AdicCompletion J R)
  let A := AdicRing.completion J fg
  let hH : J ^ (n + 1) ≤ (A.ideal ^ (n + 1)).comap φ :=
    (Ideal.pow_right_mono Ideal.le_comap_map (n + 1)).trans (Ideal.le_comap_pow _ (n + 1))
  let φₙ : CommRingCat.of (R ⧸ J ^ (n + 1)) ⟶ CommRingCat.of (A.carrier ⧸ A.ideal ^ (n + 1)) :=
    CommRingCat.ofHom (Ideal.quotientMap (A.ideal ^ (n + 1)) φ hH)
  let eM :=
    (Scheme.Modules.pullbackCongr (completionIso_hom_app J fg n).symm).hom.app
        (((CoherentFormalModule.pullback (specIso J).inv).obj M).obj n) ≫
      ((pullbackCompletionIso J fg).hom.app M).app n
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (J ^ (n + 1)))).map
      (CommRingCat.Hom.moduleSpecΓPullbackAdjoint φₙ eM) ≫
    (ModuleCat.restrictScalarsComp'App (Ideal.Quotient.mk (J ^ (n + 1))) φₙ.hom
      ((Ideal.Quotient.mk (A.ideal ^ (n + 1))).comp φ)
      (Ideal.quotientMap_comp_mk hH).symm _).inv ≫
    (ModuleCat.restrictScalarsComp'App φ (Ideal.Quotient.mk (A.ideal ^ (n + 1)))
      ((Ideal.Quotient.mk (A.ideal ^ (n + 1))).comp φ) rfl _).hom

private lemma specSectionsTowerCompletionLevelHom_apply (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) (n : ℕ)
    (m : ((specSectionsTower J).obj M).obj (op n)) :
    specSectionsTowerCompletionLevelHom J fg M n m =
      moduleSpecΓFunctor.map (((pullbackCompletionIso J fg).hom.app M).app n)
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((Spf.completionIso J fg).hom.app n)).unit.app
            (((CoherentFormalModule.pullback (specIso J).inv).obj M).obj n))
          m) := by
  refine (CommRingCat.Hom.moduleSpecΓPullbackAdjoint_apply _ _ m).trans ?_
  refine (moduleSpecΓFunctor_map_comp_apply _ _ _).trans ?_
  exact congrArg (moduleSpecΓFunctor.map (((pullbackCompletionIso J fg).hom.app M).app n))
    (moduleSpecΓFunctor_map_unit_pullbackCongr (completionIso_hom_app J fg n).symm _ m)

private instance (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) (n : ℕ) :
    IsIso (specSectionsTowerCompletionLevelHom J fg M n) := by
  let φ := algebraMap R (AdicCompletion J R)
  let A := AdicRing.completion J fg
  let hH : J ^ (n + 1) ≤ (A.ideal ^ (n + 1)).comap φ :=
    (Ideal.pow_right_mono Ideal.le_comap_map (n + 1)).trans (Ideal.le_comap_pow _ (n + 1))
  let φₙ : CommRingCat.of (R ⧸ J ^ (n + 1)) ⟶ CommRingCat.of (A.carrier ⧸ A.ideal ^ (n + 1)) :=
    CommRingCat.ofHom (Ideal.quotientMap (A.ideal ^ (n + 1)) φ hH)
  have hbij := AdicCompletion.quotientMap_algebraMap_bijective fg (n + 1) (H := hH)
  have hker : RingHom.ker φₙ.hom = ⊥ := (RingHom.injective_iff_ker_eq_bot _).1 hbij.1
  let N : (Spec (CommRingCat.of (R ⧸ J ^ (n + 1)))).Modules :=
    ((CoherentFormalModule.pullback (specIso J).inv).obj M).obj n
  have : N.IsFinitePresentation :=
    ((CoherentFormalModule.pullback (specIso J).inv).obj M).isFinitePresentation n
  have : N.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation N
  let eM :=
    (Scheme.Modules.pullbackCongr (completionIso_hom_app J fg n).symm).hom.app N ≫
      ((pullbackCompletionIso J fg).hom.app M).app n
  have hsurj := CommRingCat.Hom.moduleSpecΓFunctor_map_unit_surjective (φ := φₙ) hbij.2 N
  have hker_unit : LinearMap.ker
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φₙ)).unit.app N)).hom = ⊥ := by
    rw [CommRingCat.Hom.ker_moduleSpecΓFunctor_map_unit (φ := φₙ) hbij.2 N, hker,
      Submodule.bot_smul]
  have hinj : Function.Injective
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φₙ)).unit.app N)) :=
    LinearMap.ker_eq_bot.1 hker_unit
  have h1 : IsIso ((Scheme.Modules.pullbackCongr (completionIso_hom_app J fg n).symm).hom.app N) :=
    ((Scheme.Modules.pullbackCongr (completionIso_hom_app J fg n).symm).app N).isIso_hom
  have h2 : IsIso (((pullbackCompletionIso J fg).hom.app M).app n) :=
    @CoherentFormalModule.isIso_app_of_isIso _ _ _ ((pullbackCompletionIso J fg).hom.app M)
      ((pullbackCompletionIso J fg).app M).isIso_hom n
  have h_eM : IsIso eM := @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2
  have h_map : IsIso (moduleSpecΓFunctor.map eM) :=
    @Functor.map_isIso _ _ _ _ _ _ moduleSpecΓFunctor eM h_eM
  have he_bij : Function.Bijective (moduleSpecΓFunctor.map eM) :=
    @ConcreteCategory.bijective_of_isIso _ _ _ _ _ _ _ _ (moduleSpecΓFunctor.map eM) h_map
  have : IsIso (CommRingCat.Hom.moduleSpecΓPullbackAdjoint φₙ eM) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ?_
    have hfun : ⇑(CommRingCat.Hom.moduleSpecΓPullbackAdjoint φₙ eM) =
        ⇑(moduleSpecΓFunctor.map eM) ∘
          ⇑(moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φₙ)).unit.app N)) := by
      ext m
      exact CommRingCat.Hom.moduleSpecΓPullbackAdjoint_apply φₙ eM m
    rw [hfun]
    exact he_bij.comp ⟨hinj, hsurj⟩
  change IsIso ((ModuleCat.restrictScalars (Ideal.Quotient.mk (J ^ (n + 1)))).map
      (CommRingCat.Hom.moduleSpecΓPullbackAdjoint φₙ eM) ≫
    (ModuleCat.restrictScalarsComp'App (Ideal.Quotient.mk (J ^ (n + 1))) φₙ.hom
      ((Ideal.Quotient.mk (A.ideal ^ (n + 1))).comp φ)
      (Ideal.quotientMap_comp_mk hH).symm _).inv ≫
    (ModuleCat.restrictScalarsComp'App φ (Ideal.Quotient.mk (A.ideal ^ (n + 1)))
      ((Ideal.Quotient.mk (A.ideal ^ (n + 1))).comp φ) rfl _).hom)
  infer_instance

private lemma specSectionsTowerCompletionLevelHom_succ (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) (m : ℕ) :
    (((specSectionsTower J).obj M).map (homOfLE (Nat.le_succ m)).op) ≫
        specSectionsTowerCompletionLevelHom J fg M m =
      specSectionsTowerCompletionLevelHom J fg M (m + 1) ≫
        (ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))).map
          (((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
            ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).map
            (homOfLE (Nat.le_succ m)).op) := by
  ext x
  let M₀ := (CoherentFormalModule.pullback (specIso J).inv).obj M
  let M₁ := (CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M
  let e := (pullbackCompletionIso J fg).hom.app M
  let F := (specSectionsTower J).obj M
  let G := (CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj M₁
  have hL : (F.map (homOfLE (Nat.le_succ m)).op ≫
        specSectionsTowerCompletionLevelHom J fg M m) x =
      moduleSpecΓFunctor.map (e.app m)
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
          ((Spf.completionIso J fg).hom.app m)).unit.app (M₀.obj m))
          (moduleSpecΓFunctor.map (M₀.transitionIso m).hom
            (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
              ((spf J).ι m)).unit.app (M₀.obj (m + 1))) x))) := by
    refine (congrArg (specSectionsTowerCompletionLevelHom J fg M m)
      (LinearMap.congr_fun (TauCeti.ModuleTower.transition_def F m).symm x)).trans ?_
    refine (specSectionsTowerCompletionLevelHom_apply J fg M m (F.transition m x)).trans ?_
    exact congrArg (fun z ↦ moduleSpecΓFunctor.map (e.app m)
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
        ((Spf.completionIso J fg).hom.app m)).unit.app (M₀.obj m)) z))
      (CoherentFormalModule.sectionsTower_obj_transition_apply J M₀ m x)
  have hR : (specSectionsTowerCompletionLevelHom J fg M (m + 1) ≫
        (ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))).map
          (G.map (homOfLE (Nat.le_succ m)).op)) x =
      moduleSpecΓFunctor.map (M₁.transitionIso m).hom
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
          ((Spf (AdicRing.completion J fg)).ι m)).unit.app (M₁.obj (m + 1)))
          (moduleSpecΓFunctor.map (e.app (m + 1))
            (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
              ((Spf.completionIso J fg).hom.app (m + 1))).unit.app (M₀.obj (m + 1))) x))) := by
    refine (LinearMap.congr_fun (TauCeti.ModuleTower.transition_def G m).symm _).trans ?_
    refine (CoherentFormalModule.sectionsTower_obj_transition_apply
      (AdicRing.completion J fg).ideal M₁ m _).trans ?_
    exact congrArg (fun z ↦ moduleSpecΓFunctor.map (M₁.transitionIso m).hom
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullbackPushforwardAdjunction
        ((Spf (AdicRing.completion J fg)).ι m)).unit.app (M₁.obj (m + 1))) z))
      (specSectionsTowerCompletionLevelHom_apply J fg M (m + 1) x)
  exact hL.trans ((moduleSpecΓFunctor_map_square_transition
    ⟨(Spf.completionIso J fg).hom.naturality m⟩ (M₀.transitionIso m).hom
    (M₁.transitionIso m).hom (e.app m) (e.app (m + 1))
    ((e.naturality m).trans (Category.assoc _ _ _)) x).trans hR.symm)

private def specSectionsTowerIsoCompletion (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))) :
    (specSectionsTower J).obj M ≅
      (CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
          ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M) ⋙
        ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R)) := by
  refine NatIso.ofComponents (fun n ↦ asIso (specSectionsTowerCompletionLevelHom J fg M n.unop))
    ?_
  rintro ⟨m⟩ ⟨n⟩ ⟨h⟩
  have hle : n ≤ m := leOfHom h
  have heq : (⟨h⟩ : op m ⟶ op n) = (homOfLE hle).op := Subsingleton.elim _ _
  rw [heq]
  clear h heq
  induction m, hle using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hsucc : (homOfLE (hm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hm).op :=
      Subsingleton.elim _ _
    dsimp only [asIso_hom, Functor.comp_obj, Functor.comp_map] at ih ⊢
    rw [hsucc, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      Category.assoc, ih, ← Category.assoc,
      specSectionsTowerCompletionLevelHom_succ J fg M m, Category.assoc,
      ← CategoryTheory.Functor.map_comp]

private lemma specSectionsTowerIsoCompletion_naturality (J : Ideal R) (fg : J.FG)
    {M N : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom)))} (f : M ⟶ N) :
    ((specSectionsTower J).map f) ≫ (specSectionsTowerIsoCompletion J fg N).hom =
      (specSectionsTowerIsoCompletion J fg M).hom ≫
        Functor.whiskerRight
          ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).map
            ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f))
          (ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))) := by
  ext ⟨n⟩ x
  dsimp only [NatTrans.comp_app, specSectionsTowerIsoCompletion, NatIso.ofComponents_hom_app,
    asIso_hom, Functor.whiskerRight_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  change specSectionsTowerCompletionLevelHom J fg N n (((specSectionsTower J).map f).app (op n) x) =
    ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).map
      ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f)).app (op n)
        (specSectionsTowerCompletionLevelHom J fg M n x)
  rw [specSectionsTowerCompletionLevelHom_apply, specSectionsTowerCompletionLevelHom_apply]
  have hnatn := congrArg (·.app n) ((pullbackCompletionIso J fg).hom.naturality f)
  calc moduleSpecΓFunctor.map (((pullbackCompletionIso J fg).hom.app N).app n)
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((Spf.completionIso J fg).hom.app n)).unit.app _)
          (moduleSpecΓFunctor.map (((CoherentFormalModule.pullback (specIso J).inv).map f).app n)
            x))
      = moduleSpecΓFunctor.map (((pullbackCompletionIso J fg).hom.app N).app n)
          (moduleSpecΓFunctor.map
            ((Scheme.Modules.pullback ((Spf.completionIso J fg).hom.app n)).map
              (((CoherentFormalModule.pullback (specIso J).inv).map f).app n))
            (moduleSpecΓFunctor.map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                ((Spf.completionIso J fg).hom.app n)).unit.app _) x)) :=
        congrArg (moduleSpecΓFunctor.map (((pullbackCompletionIso J fg).hom.app N).app n))
          (moduleSpecΓFunctor_map_unit_naturality _ _ _)
    _ = moduleSpecΓFunctor.map
          ((Scheme.Modules.pullback ((Spf.completionIso J fg).hom.app n)).map
              (((CoherentFormalModule.pullback (specIso J).inv).map f).app n) ≫
            ((pullbackCompletionIso J fg).hom.app N).app n)
          (moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              ((Spf.completionIso J fg).hom.app n)).unit.app _) x) :=
        (moduleSpecΓFunctor_map_comp_apply _ _ _).symm
    _ = moduleSpecΓFunctor.map
          (((pullbackCompletionIso J fg).hom.app M).app n ≫
            ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f).app n)
          (moduleSpecΓFunctor.map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              ((Spf.completionIso J fg).hom.app n)).unit.app _) x) :=
        congrArg (fun k ↦ (moduleSpecΓFunctor.map k) _) hnatn
    _ = moduleSpecΓFunctor.map
          (((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f).app n)
          (moduleSpecΓFunctor.map (((pullbackCompletionIso J fg).hom.app M).app n)
            (moduleSpecΓFunctor.map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                ((Spf.completionIso J fg).hom.app n)).unit.app _) x)) :=
        moduleSpecΓFunctor_map_comp_apply _ _ _

/-- Under `coherentFormalModuleEquivSpecOfFG J fg`, the underlying `R`-module of the finite
`AdicCompletion J R`-module corresponding to a coherent formal module `M` on `(Spec R)/V(J)` is
naturally isomorphic to the inverse limit `specSectionsLim J` of global sections on
`(Spec R)/V(J)`. -/
def coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso (J : Ideal R) (fg : J.FG)
    [IsNoetherianRing (R ⧸ J)] :
    (coherentFormalModuleEquivSpecOfFG J fg).inverse ⋙
        (ModuleCat.isFG (AdicCompletion J R)).ι ⋙
          ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R)) ≅
      specSectionsLim J :=
  NatIso.ofComponents
    (fun M ↦
      (TauCeti.ModuleTower.limRestrictScalarsIso (algebraMap R (AdicCompletion J R))
        ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
          ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M))) ≪≫
      (TauCeti.ModuleTower.limEquivOfIso
        (specSectionsTowerIsoCompletion J fg M).symm).toModuleIso)
    fun {M N} f ↦ by
      ext x
      apply TauCeti.ModuleTower.lim_ext
      intro n
      let F_N := (specSectionsTower J).obj N
      let G_M := (CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
        ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)
      let G_N := (CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
        ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj N)
      let φ := algebraMap R (AdicCompletion J R)
      have h0 : (specSectionsTowerIsoCompletion J fg M).inv ≫ (specSectionsTower J).map f =
          Functor.whiskerRight
            ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).map
              ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f))
            (ModuleCat.restrictScalars φ) ≫
            (specSectionsTowerIsoCompletion J fg N).inv := by
        rw [Iso.inv_comp_eq, ← Category.assoc,
          ← specSectionsTowerIsoCompletion_naturality J fg f, Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
      have hval : (((specSectionsTower J).map f).app (op n)).hom
            (((specSectionsTowerIsoCompletion J fg M).inv.app (op n)).hom (G_M.limπ n x)) =
          ((specSectionsTowerIsoCompletion J fg N).inv.app (op n)).hom
            ((((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).map
              ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f)).app
                (op n)).hom (G_M.limπ n x)) :=
        congrArg (fun k ↦ (k.app (op n)).hom (G_M.limπ n x)) h0
      have hL : F_N.limπ n
          ((((coherentFormalModuleEquivSpecOfFG J fg).inverse ⋙
            (ModuleCat.isFG (AdicCompletion J R)).ι ⋙ ModuleCat.restrictScalars φ).map f ≫
              (TauCeti.ModuleTower.limRestrictScalarsIso φ G_N ≪≫
                (TauCeti.ModuleTower.limEquivOfIso
                  (specSectionsTowerIsoCompletion J fg N).symm).toModuleIso).hom) x) =
          ((specSectionsTowerIsoCompletion J fg N).inv.app (op n)).hom
            ((((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).map
              ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f)).app
                (op n)).hom (G_M.limπ n x)) := by
        have heq :
            ((((coherentFormalModuleEquivSpecOfFG J fg).inverse ⋙
              (ModuleCat.isFG (AdicCompletion J R)).ι ⋙ ModuleCat.restrictScalars φ).map f ≫
                (TauCeti.ModuleTower.limRestrictScalarsIso φ G_N ≪≫
                  (TauCeti.ModuleTower.limEquivOfIso
                    (specSectionsTowerIsoCompletion J fg N).symm).toModuleIso).hom) x) =
            TauCeti.ModuleTower.limMap (specSectionsTowerIsoCompletion J fg N).inv
              ((TauCeti.ModuleTower.limRestrictScalarsIso φ G_N).hom
                (TauCeti.ModuleTower.limMap
                  ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).map
                    ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).map f)) x)) :=
          TauCeti.ModuleTower.limEquivOfIso_apply (specSectionsTowerIsoCompletion J fg N).symm _
        refine (congrArg (F_N.limπ n) heq).trans ?_
        refine (LinearMap.congr_fun
          (TauCeti.ModuleTower.limπ_comp_limMap (specSectionsTowerIsoCompletion J fg N).inv n)
          _).trans ?_
        refine (congrArg (fun z ↦ ((specSectionsTowerIsoCompletion J fg N).inv.app (op n)).hom z)
          (TauCeti.ModuleTower.limπ_limRestrictScalarsIso_hom φ G_N n _)).trans ?_
        exact congrArg (fun z ↦ ((specSectionsTowerIsoCompletion J fg N).inv.app (op n)).hom z)
          (LinearMap.congr_fun (TauCeti.ModuleTower.limπ_comp_limMap _ n) x)
      have hR : F_N.limπ n
          (((TauCeti.ModuleTower.limRestrictScalarsIso φ G_M ≪≫
            (TauCeti.ModuleTower.limEquivOfIso
              (specSectionsTowerIsoCompletion J fg M).symm).toModuleIso).hom ≫
            (specSectionsLim J).map f) x) =
          (((specSectionsTower J).map f).app (op n)).hom
            (((specSectionsTowerIsoCompletion J fg M).inv.app (op n)).hom (G_M.limπ n x)) := by
        refine (LinearMap.congr_fun (TauCeti.ModuleTower.limπ_comp_limMap
          ((specSectionsTower J).map f) n) _).trans ?_
        refine congrArg (fun z ↦ (((specSectionsTower J).map f).app (op n)).hom z) ?_
        have heq :
            (TauCeti.ModuleTower.limRestrictScalarsIso φ G_M ≪≫
              (TauCeti.ModuleTower.limEquivOfIso
                (specSectionsTowerIsoCompletion J fg M).symm).toModuleIso).hom x =
            TauCeti.ModuleTower.limMap (specSectionsTowerIsoCompletion J fg M).inv
              ((TauCeti.ModuleTower.limRestrictScalarsIso φ G_M).hom x) :=
          TauCeti.ModuleTower.limEquivOfIso_apply
            (specSectionsTowerIsoCompletion J fg M).symm
            ((TauCeti.ModuleTower.limRestrictScalarsIso φ G_M).hom x)
        refine (congrArg (TauCeti.ModuleTower.limπ ((specSectionsTower J).obj M) n) heq).trans ?_
        refine (LinearMap.congr_fun (TauCeti.ModuleTower.limπ_comp_limMap
          (specSectionsTowerIsoCompletion J fg M).inv n) _).trans ?_
        exact congrArg (fun z ↦ ((specSectionsTowerIsoCompletion J fg M).inv.app (op n)).hom z)
          (TauCeti.ModuleTower.limπ_limRestrictScalarsIso_hom φ G_M n x)
      exact hL.trans (hval.symm.trans hR.symm)

/-- On level-`n` projections, the inverse of
`coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg` pulls a global section back
along `(Spf.completionIso J fg).hom.app n` and applies the pullback coherence isomorphism. -/
theorem coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso_inv_app_limπ
    (J : Ideal R) (fg : J.FG) [IsNoetherianRing (R ⧸ J)]
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ) (y : ((specSectionsTower J).obj M).lim) :
    ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
        ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).limπ n
      ((coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg).inv.app M y) =
      moduleSpecΓFunctor.map
        (((CoherentFormalModule.pullbackComp (Spf.completionIso J fg).hom
            (specIso J).inv).hom.app M).app n ≫
          ((CoherentFormalModule.pullbackCongr
            (specIsoSpfCompletion_inv J fg).symm).hom.app M).app n)
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((Spf.completionIso J fg).hom.app n)).unit.app
            (((CoherentFormalModule.pullback (specIso J).inv).obj M).obj n))
          (((specSectionsTower J).obj M).limπ n y)) := by
  refine Eq.trans ?_
    (specSectionsTowerCompletionLevelHom_apply J fg M n (((specSectionsTower J).obj M).limπ n y))
  have h1 : ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
      ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).limπ n
        ((coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg).inv.app M y) =
      TauCeti.ModuleTower.limπ
        (((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
          ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)) ⋙
            ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R))) n
        ((TauCeti.ModuleTower.limEquivOfIso
          (specSectionsTowerIsoCompletion J fg M).symm).symm y) :=
    TauCeti.ModuleTower.limπ_limRestrictScalarsIso_inv _ _ n _
  refine h1.trans ?_
  rw [TauCeti.ModuleTower.limEquivOfIso_symm_apply]
  exact LinearMap.congr_fun (TauCeti.ModuleTower.limπ_comp_limMap _ n) y

private lemma pullbackCompletionIso_comp_eq (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (h_eq : (Spf.completionIso J fg).inv ≫ (specIsoSpfCompletion J fg).inv = (specIso J).inv) :
    (CoherentFormalModule.pullback (Spf.completionIso J fg).inv).map
        ((pullbackCompletionIso J fg).hom.app M) ≫
      (CoherentFormalModule.pullbackComp (Spf.completionIso J fg).inv
        (specIsoSpfCompletion J fg).inv).hom.app M ≫
        (CoherentFormalModule.pullbackCongr h_eq).hom.app M =
    (CoherentFormalModule.pullbackComp (Spf.completionIso J fg).inv
        (Spf.completionIso J fg).hom).hom.app
        ((CoherentFormalModule.pullback (specIso J).inv).obj M) ≫
      (CoherentFormalModule.pullbackCongr (Spf.completionIso J fg).inv_hom_id).hom.app
        ((CoherentFormalModule.pullback (specIso J).inv).obj M) ≫
        (CoherentFormalModule.pullbackId _).hom.app
          ((CoherentFormalModule.pullback (specIso J).inv).obj M) := by
  let f := (Spf.completionIso J fg).inv
  let g := (Spf.completionIso J fg).hom
  let h := (specIso J).inv
  dsimp only [pullbackCompletionIso, Iso.trans_hom, NatTrans.comp_app]
  rw [CategoryTheory.Functor.map_comp, Category.assoc]
  have hcongr1 := congrArg (fun τ ↦ τ.app M)
    (CoherentFormalModule.pullbackComp_hom_comp_pullbackCongr_hom f
      (specIsoSpfCompletion_inv J fg).symm)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hcongr1
  rw [← Category.assoc ((CoherentFormalModule.pullback f).map
      ((CoherentFormalModule.pullbackCongr _).hom.app M)),
    hcongr1, Category.assoc]
  have htrans0 := congrArg (fun τ ↦ τ.hom.app M)
    (CoherentFormalModule.pullbackCongr_trans
      (congrArg (f ≫ ·) (specIsoSpfCompletion_inv J fg).symm) h_eq)
  dsimp only [Iso.trans_hom, NatTrans.comp_app] at htrans0
  rw [← htrans0, ← CoherentFormalModule.pullbackComp_assoc_app_assoc f g h M]
  have htrans := congrArg (fun τ ↦ τ.hom.app M)
    (CoherentFormalModule.pullbackCongr_trans (Category.assoc f g h)
      ((congrArg (f ≫ ·) (specIsoSpfCompletion_inv J fg).symm).trans h_eq))
  have htrans2 := congrArg (fun τ ↦ τ.hom.app M)
    (CoherentFormalModule.pullbackCongr_trans
      (congrArg (· ≫ h) (Spf.completionIso J fg).inv_hom_id) (Category.id_comp h))
  have hcongr := congrArg (fun τ ↦ τ.app M)
    (CoherentFormalModule.pullbackCongr_hom_whiskerLeft_pullbackComp_hom
      (Spf.completionIso J fg).inv_hom_id h)
  have hid := CoherentFormalModule.pullback_id_comp_app h M
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.whiskerLeft_app] at htrans htrans2 hcongr
  rw [← htrans, htrans2, ← Category.assoc _ ((CoherentFormalModule.pullbackCongr _).hom.app _),
    ← hcongr, Category.assoc, hid]

private lemma completionIso_inv_hom_id_app (J : Ideal R) (fg : J.FG) (n : ℕ) :
    (Spf.completionIso J fg).inv.app n ≫ (Spf.completionIso J fg).hom.app n =
      𝟙 ((spf J).X n) := by
  rw [← AdicThickeningSystem.comp_app, (Spf.completionIso J fg).inv_hom_id,
    AdicThickeningSystem.id_app]

private lemma pullbackCompletionIso_comp_eq_app (J : Ideal R) (fg : J.FG)
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ)
    (h_eq : (Spf.completionIso J fg).inv ≫ (specIsoSpfCompletion J fg).inv = (specIso J).inv) :
    (Scheme.Modules.pullback ((Spf.completionIso J fg).inv.app n)).map
        (((pullbackCompletionIso J fg).hom.app M).app n) ≫
      ((CoherentFormalModule.pullbackComp (Spf.completionIso J fg).inv
        (specIsoSpfCompletion J fg).inv).hom.app M).app n ≫
        ((CoherentFormalModule.pullbackCongr h_eq).hom.app M).app n =
      (Scheme.Modules.pullbackCompIsoId (completionIso_inv_hom_id_app J fg n)).hom.app
        (((CoherentFormalModule.pullback (specIso J).inv).obj M).obj n) := by
  have hn := congrArg (·.app n) (pullbackCompletionIso_comp_eq J fg M h_eq)
  simp only [CoherentFormalModule.comp_app, CoherentFormalModule.pullback_map_app] at hn
  exact hn.trans
    (CoherentFormalModule.pullbackComp_hom_comp_pullbackCongr_hom_comp_pullbackId_hom_app_app
      (Spf.completionIso J fg).inv_hom_id _ n)

/-- On level-`n` projections,
`coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg` pulls a global section back
along `(Spf.completionIso J fg).inv.app n` and applies the pullback coherence isomorphism. -/
theorem coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso_hom_app_limπ
    (J : Ideal R) (fg : J.FG) [IsNoetherianRing (R ⧸ J)]
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ)
    (x : ((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
      ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).lim) :
    ((specSectionsTower J).obj M).limπ n
      ((coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg).hom.app M x) =
      moduleSpecΓFunctor.map
        (((CoherentFormalModule.pullbackComp (Spf.completionIso J fg).inv
            (specIsoSpfCompletion J fg).inv).hom.app M).app n ≫
          ((CoherentFormalModule.pullbackCongr
            (completionIso_inv_comp_specIsoSpfCompletion_inv J fg)).hom.app M).app n)
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((Spf.completionIso J fg).inv.app n)).unit.app
            (((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M).obj n))
          (((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
            ((CoherentFormalModule.pullback
              (specIsoSpfCompletion J fg).inv).obj M)).limπ n x)) := by
  have hx : (coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg).inv.app M
      ((coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg).hom.app M x) = x :=
    ConcreteCategory.congr_hom
      (Iso.hom_inv_id_app (coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg) M)
      x
  have hπ := congrArg
    (((CoherentFormalModule.sectionsTower (AdicRing.completion J fg).ideal).obj
      ((CoherentFormalModule.pullback (specIsoSpfCompletion J fg).inv).obj M)).limπ n) hx
  have hπ' := coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso_inv_app_limπ J fg M n
    ((coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J fg).hom.app M x)
  exact moduleSpecΓFunctor_map_inv_hom_cancel (completionIso_inv_hom_id_app J fg n)
    (((pullbackCompletionIso J fg).hom.app M).app n)
    (((CoherentFormalModule.pullbackComp (Spf.completionIso J fg).inv
        (specIsoSpfCompletion J fg).inv).hom.app M).app n ≫
      ((CoherentFormalModule.pullbackCongr
        (completionIso_inv_comp_specIsoSpfCompletion_inv J fg)).hom.app M).app n)
    (pullbackCompletionIso_comp_eq_app J fg M n
      (completionIso_inv_comp_specIsoSpfCompletion_inv J fg)) _ _ (hπ'.symm.trans hπ)

end

end AlgebraicGeometry.Scheme.formalCompletion
