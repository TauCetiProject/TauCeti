/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pushforward
public import TauCeti.Topology.Sheaves.Stalks

import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Stalk
import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Identity
import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Stalk

/-!
# Strong symmetric monoidal pullback

For an arbitrary morphism of ringed spaces, the canonical oplax tensor comparison for pullback
of sheaves of modules is an isomorphism. On stalks this is the standard equivalence distributing
extension of scalars over tensor products (Stacks Project, Tag 01CD).

The inverse tensor and unit comparisons make pullback strong symmetric monoidal. The canonical
identity and composition isomorphisms of pullback are monoidal for these structures.
-/

public section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace TauCeti.SheafOfModules

noncomputable section

private def tensorStalkEquivMonoidal {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) (x : X) :
    ↑(TopCat.Presheaf.stalk (M ⊗ N).val.presheaf x) ≃ₗ[
      ↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk M.val.presheaf x) ⊗[↑(TopCat.Presheaf.stalk R.obj x)]
        ↑(TopCat.Presheaf.stalk N.val.presheaf x) :=
  let e := M.tensorUnderlyingIso N ≪≫ (tensorProductIso R M N).symm
  let eStalk := LinearEquiv.ofBijective
    (PresheafOfModules.stalkMapCommRing (S := R.obj) x e.hom.val) (by
      have : IsIso e.hom.val :=
        inferInstanceAs (IsIso ((_root_.SheafOfModules.forget _).map e.hom))
      apply (congrArg Function.Bijective
        (PresheafOfModules.coe_stalkMapCommRing (S := R.obj) x e.hom.val)).mpr
      exact (ConcreteCategory.isIso_iff_bijective _).mp (by infer_instance))
  eStalk ≪≫ₗ tensorStalkEquiv R M N x

private lemma tensorStalkEquivMonoidal_germ {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
    (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) (x : X)
    (U : Opens X) (hx : x ∈ U) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, Functor.id_obj, Functor.comp_obj]
    (tensorStalkEquivMonoidal R M N x
      (TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
        ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app
          (op U) (m ⊗ₜ[R.obj.obj (op U)] n))) =
      TopCat.Presheaf.germ M.val.presheaf U x hx m ⊗ₜ[↑(TopCat.Presheaf.stalk R.obj x)]
        TopCat.Presheaf.germ N.val.presheaf U x hx n) := by
  have h : Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N ≫
      (_root_.SheafOfModules.forget (ringCatSheaf R)).map
        (M.tensorUnderlyingIso N ≪≫ (tensorProductIso R M N).symm).hom =
      (sheafificationForgetAdjunction R).unit.app (M.val ⊗ N.val) ≫
        (_root_.SheafOfModules.forget (ringCatSheaf R)).map (tensorProductIso R M N).inv := by
    have he : (_root_.SheafOfModules.forget (ringCatSheaf R)).map
        (M.tensorUnderlyingIso N).inv ≫
        (_root_.SheafOfModules.forget (ringCatSheaf R)).map
          (M.tensorUnderlyingIso N ≪≫ (tensorProductIso R M N).symm).hom =
        (_root_.SheafOfModules.forget (ringCatSheaf R)).map (tensorProductIso R M N).inv := by
      rw [← Functor.map_comp]
      simp
      rfl
    exact (congrArg (· ≫ _) (forget_μ (R := R) M N)).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) he))
  -- The monoidal tensor and the sheafified sectionwise tensor have different presentations.
  -- Their stalk modules agree after reading the canonical tensor isomorphism as a linear map.
  change tensorStalkEquiv R M N x
    (PresheafOfModules.stalkMapCommRing (S := R.obj) x
      (M.tensorUnderlyingIso N ≪≫ (tensorProductIso R M N).symm).hom.val
      (TopCat.Presheaf.germ (M ⊗ N).val.presheaf U x hx
        ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf R)) M N).app
          (op U) (m ⊗ₜ[R.obj.obj (op U)] n)))) = _
  erw [PresheafOfModules.stalkMapCommRing_germ]
  refine (congrArg (fun k : M.val ⊗ N.val ⟶ (tensorProduct R M N).val ↦
    tensorStalkEquiv R M N x (TopCat.Presheaf.germ (tensorProduct R M N).val.presheaf
      U x hx (k.app (op U) (m ⊗ₜ[R.obj.obj (op U)] n)))) h).trans ?_
  rw [tensorStalkEquiv_apply]
  rw [sheafificationForgetAdjunction_unit_app (R := R) (M.val ⊗ N.val)]
  dsimp only [_root_.SheafOfModules.forget_obj, Functor.id_obj]
  exact tensorStalkComparison_germ_unit_tmul R M N x U hx m n

variable {X Y : TopCat.{u}} {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} {f : Y ⟶ X}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]
  (M N : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X))

private lemma pullback_δ_unit_tensor (U : Opens X)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val.app
      (op ((Opens.map f).obj U))
      (pullbackUnitApp φ (M ⊗ N) U
        ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) M N).app
          (op U) (m ⊗ₜ[𝒪X.obj.obj (op U)] n))) =
      (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪Y))
        ((_root_.SheafOfModules.pullback φ).obj M)
        ((_root_.SheafOfModules.pullback φ).obj N)).app (op ((Opens.map f).obj U))
          (pullbackUnitApp φ M U m ⊗ₜ[𝒪Y.obj.obj (op ((Opens.map f).obj U))]
            pullbackUnitApp φ N U n) := by
  let adj := _root_.SheafOfModules.pullbackPushforwardAdjunction φ
  have h : adj.unit.app (M ⊗ N) ≫
      (_root_.SheafOfModules.pushforward φ).map
        (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N) =
      (adj.unit.app M ⊗ₘ adj.unit.app N) ≫
        Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward φ) _ _ := by
    exact (_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit_app_tensor_comp_map_δ M N
  have hh := congrArg (fun k ↦
    (Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) M N) ≫
      (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)).map k) h
  simp only [Functor.map_comp] at hh
  erw [← Functor.LaxMonoidal.μ_natural_assoc] at hh
  have he := congrArg (fun k ↦ k.app (op U) (m ⊗ₜ[𝒪X.obj.obj (op U)] n)) hh
  -- On sections the presheaf pushforward uses the same carriers, with scalars restricted.
  change _ = (Functor.LaxMonoidal.μ (_root_.SheafOfModules.pushforward φ) _ _).val.app
    (op U) ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X))
      ((_root_.SheafOfModules.pushforward φ).obj ((_root_.SheafOfModules.pullback φ).obj M))
      ((_root_.SheafOfModules.pushforward φ).obj ((_root_.SheafOfModules.pullback φ).obj N))).app
        (op U) (pullbackUnitApp φ M U m ⊗ₜ[𝒪X.obj.obj (op U)]
          pullbackUnitApp φ N U n)) at he
  exact he.trans (_root_.SheafOfModules.pushforward_μ_app_tmul
    (S := 𝒪X) (R := 𝒪Y) φ _ _ (op U) _ _)

private def pullbackTensorStalkSource (y : Y) :
    letI := stalkAlgebra φ y
    ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) ⊗[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
      (↑(TopCat.Presheaf.stalk M.val.presheaf (f y)) ⊗[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
        ↑(TopCat.Presheaf.stalk N.val.presheaf (f y)))
      ≃ₗ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)]
        ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback φ).obj (M ⊗ N)).val.presheaf y) :=
  letI := stalkAlgebra φ y
  (tensorStalkEquivMonoidal 𝒪X M N (f y)).symm.baseChange _ _ ≪≫ₗ
    pullbackStalkEquiv φ (M ⊗ N) y

private def pullbackTensorStalkTarget (y : Y) :
    letI := stalkAlgebra φ y
    ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) ⊗[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
      (↑(TopCat.Presheaf.stalk M.val.presheaf (f y)) ⊗[↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))]
        ↑(TopCat.Presheaf.stalk N.val.presheaf (f y)))
      ≃ₗ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)]
        ↑(TopCat.Presheaf.stalk
          (((_root_.SheafOfModules.pullback φ).obj M) ⊗
            ((_root_.SheafOfModules.pullback φ).obj N)).val.presheaf y) :=
  letI := stalkAlgebra φ y
  TensorProduct.AlgebraTensorModule.distribBaseChange _ _ _ _ ≪≫ₗ
    TensorProduct.congr (pullbackStalkEquiv φ M y) (pullbackStalkEquiv φ N y) ≪≫ₗ
      (tensorStalkEquivMonoidal 𝒪Y ((_root_.SheafOfModules.pullback φ).obj M)
        ((_root_.SheafOfModules.pullback φ).obj N) y).symm

private def pullbackTensorStalkEquiv (y : Y) :
    ↑(TopCat.Presheaf.stalk ((_root_.SheafOfModules.pullback φ).obj (M ⊗ N)).val.presheaf y)
      ≃ₗ[↑(TopCat.Presheaf.stalk 𝒪Y.obj y)]
        ↑(TopCat.Presheaf.stalk
          (((_root_.SheafOfModules.pullback φ).obj M) ⊗
            ((_root_.SheafOfModules.pullback φ).obj N)).val.presheaf y) :=
  (pullbackTensorStalkSource φ M N y).symm ≪≫ₗ pullbackTensorStalkTarget φ M N y

private lemma pullback_δ_stalk_germ (y : Y) (a : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y))
    (U : Opens X) (hy : f y ∈ U) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    dsimp% only [PresheafOfModules.presheaf_obj_coe, Functor.id_obj, Functor.comp_obj]
    (tensorStalkEquivMonoidal 𝒪Y ((_root_.SheafOfModules.pullback φ).obj M)
      ((_root_.SheafOfModules.pullback φ).obj N) y
      (PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
        (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val
        (a • TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback φ).obj (M ⊗ N)).val.presheaf
          ((Opens.map f).obj U) y hy (pullbackUnitApp φ (M ⊗ N) U
            ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) M N).app
              (op U) (m ⊗ₜ[𝒪X.obj.obj (op U)] n))))) =
      a • (TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback φ).obj M).val.presheaf
        ((Opens.map f).obj U) y hy (pullbackUnitApp φ M U m) ⊗ₜ
        TopCat.Presheaf.germ ((_root_.SheafOfModules.pullback φ).obj N).val.presheaf
          ((Opens.map f).obj U) y hy (pullbackUnitApp φ N U n))) := by
  let β := tensorStalkEquivMonoidal 𝒪Y ((_root_.SheafOfModules.pullback φ).obj M)
    ((_root_.SheafOfModules.pullback φ).obj N) y
  let d := PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
    (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val
  refine (congrArg β (d.map_smul a _)).trans ((β.map_smul a _).trans ?_)
  have hd := PresheafOfModules.stalkMapCommRing_germ (S := 𝒪Y.obj) y
    (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val
    ((Opens.map f).obj U) hy
    (pullbackUnitApp φ (M ⊗ N) U
      ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) M N).app
        (op U) (m ⊗ₜ[𝒪X.obj.obj (op U)] n)))
  refine (congrArg (fun t ↦ a • β t) hd).trans ?_
  rw [pullback_δ_unit_tensor φ M N U m n]
  exact congrArg (a • ·) (tensorStalkEquivMonoidal_germ 𝒪Y
    ((_root_.SheafOfModules.pullback φ).obj M)
    ((_root_.SheafOfModules.pullback φ).obj N) y ((Opens.map f).obj U) hy
    (pullbackUnitApp φ M U m) (pullbackUnitApp φ N U n))

private lemma pullbackTensorStalk_germ (y : Y) (a : ↑(TopCat.Presheaf.stalk 𝒪Y.obj y))
    (U : Opens X) (hy : f y ∈ U) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    letI := stalkAlgebra φ y
    PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
      (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val
      (pullbackTensorStalkSource φ M N y (a ⊗ₜ
        (TopCat.Presheaf.germ M.val.presheaf U (f y) hy m ⊗ₜ
          TopCat.Presheaf.germ N.val.presheaf U (f y) hy n))) =
      pullbackTensorStalkTarget φ M N y (a ⊗ₜ
        (TopCat.Presheaf.germ M.val.presheaf U (f y) hy m ⊗ₜ
          TopCat.Presheaf.germ N.val.presheaf U (f y) hy n)) := by
  let := stalkAlgebra φ y
  let α := tensorStalkEquivMonoidal 𝒪X M N (f y)
  let β := tensorStalkEquivMonoidal 𝒪Y ((_root_.SheafOfModules.pullback φ).obj M)
    ((_root_.SheafOfModules.pullback φ).obj N) y
  let p := pullbackStalkEquiv φ (M ⊗ N) y
  let d := PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
    (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val
  let b := TensorProduct.AlgebraTensorModule.distribBaseChange
    (↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))) (↑(TopCat.Presheaf.stalk 𝒪Y.obj y))
    (↑(TopCat.Presheaf.stalk M.val.presheaf (f y)))
    (↑(TopCat.Presheaf.stalk N.val.presheaf (f y)))
  let c := TensorProduct.congr (pullbackStalkEquiv φ M y) (pullbackStalkEquiv φ N y)
  -- Expand only the comparison equivalences on this pure tensor to apply their germ formulas.
  change d (p (a ⊗ₜ α.symm
    (TopCat.Presheaf.germ M.val.presheaf U (f y) hy m ⊗ₜ
      TopCat.Presheaf.germ N.val.presheaf U (f y) hy n))) =
    β.symm (c (b (a ⊗ₜ (TopCat.Presheaf.germ M.val.presheaf U (f y) hy m ⊗ₜ
      TopCat.Presheaf.germ N.val.presheaf U (f y) hy n))))
  have hα : α.symm
      (TopCat.Presheaf.germ M.val.presheaf U (f y) hy m ⊗ₜ
        TopCat.Presheaf.germ N.val.presheaf U (f y) hy n) =
      TopCat.Presheaf.germ (M ⊗ N).val.presheaf U (f y) hy
        ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) M N).app
          (op U) (m ⊗ₜ[𝒪X.obj.obj (op U)] n)) :=
    α.symm_apply_eq.mpr (tensorStalkEquivMonoidal_germ 𝒪X M N (f y) U hy m n).symm
  rw [hα]
  refine (congrArg d (pullbackStalkEquiv_tmul_germ φ (M ⊗ N) y a U hy
    ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) M N).app
      (op U) (m ⊗ₜ[𝒪X.obj.obj (op U)] n)))).trans ?_
  apply β.injective
  refine Eq.trans ?_ (β.apply_symm_apply _).symm
  refine (pullback_δ_stalk_germ φ M N y a U hy m n).trans ?_
  dsimp only [b, c]
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  refine Eq.trans ?_ (TensorProduct.congr_tmul (pullbackStalkEquiv φ M y)
    (pullbackStalkEquiv φ N y)
    (a ⊗ₜ TopCat.Presheaf.germ M.val.presheaf U (f y) hy m)
    (1 ⊗ₜ TopCat.Presheaf.germ N.val.presheaf U (f y) hy n)).symm
  refine Eq.trans ?_ (congrArg₂ (TensorProduct.tmul (↑(TopCat.Presheaf.stalk 𝒪Y.obj y)))
    (pullbackStalkEquiv_tmul_germ φ M y a U hy m)
    (pullbackStalkEquiv_tmul_germ φ N y 1 U hy n)).symm
  rw [one_smul, TensorProduct.smul_tmul']

private lemma pullbackTensorStalkEquiv_eq (y : Y) :
    PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
      (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val =
      (pullbackTensorStalkEquiv φ M N y).toLinearMap := by
  let := stalkAlgebra φ y
  let e := pullbackTensorStalkSource φ M N y
  let D := (PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
    (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val).comp e.toLinearMap
  let H := (pullbackTensorStalkTarget φ M N y).toLinearMap
  apply (LinearMap.cancel_right e.surjective).mp
  have h : (pullbackTensorStalkEquiv φ M N y).toLinearMap.comp e.toLinearMap = H := by
    apply LinearMap.ext
    intro t
    -- In the comparison composite, the source equivalence immediately cancels its inverse.
    change pullbackTensorStalkTarget φ M N y (e.symm (e t)) = H t
    rw [e.symm_apply_apply t]
    rfl
  have hleft : D = H := by
    let A := ↑(TopCat.Presheaf.stalk 𝒪X.obj (f y))
    let B := ↑(TopCat.Presheaf.stalk 𝒪Y.obj y)
    let T := ↑(TopCat.Presheaf.stalk
      (((_root_.SheafOfModules.pullback φ).obj M) ⊗
        ((_root_.SheafOfModules.pullback φ).obj N)).val.presheaf y)
    let : Module A T := Module.compHom T (algebraMap A B)
    let : IsScalarTower A B T := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    -- A linear map out of the scalar extension is determined on tensors with coefficient one.
    apply (LinearMap.liftBaseChangeEquiv B).symm.injective
    apply TensorProduct.ext'
    intro m n
    simp only [LinearMap.liftBaseChangeEquiv_symm_apply]
    obtain ⟨U, hy, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf m
    obtain ⟨V, hVU, hyV, n, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq N.val.presheaf n hy
    rw [← TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE hVU) (f y) hyV m]
    exact pullbackTensorStalk_germ φ M N y 1 V hyV (M.val.map (homOfLE hVU).op m) n
  exact hleft.trans h.symm

/-- The canonical tensor comparison for pullback of arbitrary sheaves of modules along a
morphism of ringed spaces is an isomorphism. -/
instance isIso_pullback_δ :
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N) := by
  suffices IsIso ((_root_.SheafOfModules.toSheaf (ringCatSheaf 𝒪Y)).map
      (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N)) by
    exact isIso_of_reflects_iso _ (_root_.SheafOfModules.toSheaf (ringCatSheaf 𝒪Y))
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  intro y
  rw [ConcreteCategory.isIso_iff_bijective]
  -- Express the forgotten sheaf morphism through its underlying module presheaf.
  change Function.Bijective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat y).map
    ((PresheafOfModules.toPresheaf _).map
      (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val))
  have hb : Function.Bijective (PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
      (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val) := by
    rw [pullbackTensorStalkEquiv_eq φ M N y]
    exact (pullbackTensorStalkEquiv φ M N y).bijective
  exact (congrArg Function.Bijective (PresheafOfModules.coe_stalkMapCommRing
    (S := 𝒪Y.obj) y (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val)).mp hb

/-- Pullback along a morphism of ringed spaces is strong symmetric monoidal, with its tensor
and unit maps inverse to the canonical oplax comparisons. -/
instance pullbackBraided : (_root_.SheafOfModules.pullback.{u} φ).Braided := by
  have : IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} φ)) :=
    (_root_.SheafOfModules.pullback_η φ).symm ▸
      _root_.SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal φ
  letI : (_root_.SheafOfModules.pullback.{u} φ).Monoidal :=
    Functor.Monoidal.ofOplaxMonoidal _
  exact (_root_.SheafOfModules.pullbackPushforwardAdjunction φ).leftAdjointBraided

/-- The unit comparison for strong monoidal pullback is the inverse of the canonical map
from the pullback of the structure sheaf to the structure sheaf. -/
@[simp]
theorem pullback_ε :
    haveI := _root_.SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal φ
    Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u} φ) =
      inv (_root_.SheafOfModules.pullbackObjUnitToUnit φ) := by
  have := _root_.SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal φ
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← _root_.SheafOfModules.pullback_η φ]
  exact Functor.Monoidal.η_ε (_root_.SheafOfModules.pullback.{u} φ)

section Coherence

open _root_.SheafOfModules
open Functor.OplaxMonoidal Functor.LaxMonoidal

/-- The canonical comparison from identity pullback to the identity functor is monoidal. -/
theorem isMonoidal_pullbackId_hom
    (R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}) :
    let b := @pullbackBraided X X R R (𝟙 X) (𝟙 (ringCatSheaf R))
      (Functor.isRightAdjoint_of_iso (pushforwardId (ringCatSheaf R)).symm)
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (pullbackId.{u} (ringCatSheaf R)).hom
      b.toMonoidal.toLaxMonoidal Functor.LaxMonoidal.id := by
  dsimp only
  let F := pullback.{u} (F := 𝟭 (Opens X)) (R := ringCatSheaf R) (𝟙 (ringCatSheaf R))
  let b : F.Braided := @pullbackBraided X X R R (𝟙 X) (𝟙 (ringCatSheaf R))
    (Functor.isRightAdjoint_of_iso (pushforwardId (ringCatSheaf R)).symm)
  let : F.Monoidal := b.toMonoidal
  refine ⟨?_, fun M N ↦ ?_⟩
  · rw [← pullback_id_η R]
    exact Functor.Monoidal.ε_η F
  · rw [← cancel_epi (δ F M N)]
    dsimp only [F]
    rw [Functor.Monoidal.δ_μ_assoc, Functor.LaxMonoidal.id_μ, Category.comp_id]
    exact (pullback_id_δ R M N).symm

variable {Z : TopCat.{u}} {𝒪Z : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u}}
  {g : Z ⟶ Y}
  (ψ : ringCatSheaf 𝒪Y ⟶
    ((Opens.map g).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Z))
  [(pushforward.{u} ψ).IsRightAdjoint]

/-- The canonical comparison from iterated pullback to pullback along the composite is
monoidal. -/
theorem isMonoidal_pullbackComp_hom :
    let θ := φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).map ψ
    let := (pullbackBraided φ).toMonoidal
    let := (pullbackBraided ψ).toMonoidal
    let b := @pullbackBraided X Z 𝒪X 𝒪Z (g ≫ f) θ
      (Functor.isRightAdjoint_of_iso (pushforwardComp.{u} φ ψ))
    @NatTrans.IsMonoidal _ _ _ _ _ _ _ _ (pullbackComp.{u} φ ψ).hom
      (Functor.LaxMonoidal.comp (pullback.{u} φ) (pullback.{u} ψ))
      b.toMonoidal.toLaxMonoidal := by
  dsimp only
  let G := pullback.{u} (F := Opens.map f ⋙ Opens.map g) (R := ringCatSheaf 𝒪Z)
    (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).map ψ)
  let b : G.Braided := @pullbackBraided X Z 𝒪X 𝒪Z (g ≫ f)
    (φ ≫ ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).map ψ)
    (Functor.isRightAdjoint_of_iso (pushforwardComp.{u} φ ψ))
  let := (pullbackBraided φ).toMonoidal
  let := (pullbackBraided ψ).toMonoidal
  let : G.Monoidal := b.toMonoidal
  let e := pullbackComp.{u} φ ψ
  have hεη : ε G ≫ η G = 𝟙 _ := b.toMonoidal.ε_η
  let : IsIso (η G) := ⟨⟨ε G, b.toMonoidal.η_ε, hεη⟩⟩
  have hη : e.hom.app (𝟙_ _) ≫ η G = η (pullback.{u} φ ⋙ pullback.{u} ψ) := by
    dsimp only [G]
    rw [pullback_comp_η φ ψ]
    simp only [e, Iso.hom_inv_id_app_assoc, Functor.OplaxMonoidal.comp_η]
  have hδ (M N) : e.hom.app (M ⊗ N) ≫ δ G M N =
      δ (pullback.{u} φ ⋙ pullback.{u} ψ) M N ≫ (e.hom.app M ⊗ₘ e.hom.app N) := by
    dsimp only [G]
    rw [pullback_comp_δ φ ψ M N]
    simp only [e, Iso.hom_inv_id_app_assoc, Functor.OplaxMonoidal.comp_δ, Category.assoc]
  refine ⟨?_, fun M N ↦ ?_⟩
  · rw [← cancel_mono (η G), Category.assoc, hη]
    -- The comparison in the goal and the named functor `G` use the same composite site.
    erw [hεη]
    exact Functor.Monoidal.ε_η (pullback.{u} φ ⋙ pullback.{u} ψ)
  · have hμδ : μ G M N ≫ δ G M N = 𝟙 _ := b.toMonoidal.μ_δ M N
    let : IsIso (δ G M N) := ⟨⟨μ G M N, b.toMonoidal.δ_μ M N, hμδ⟩⟩
    rw [← cancel_epi (δ (pullback.{u} φ ⋙ pullback.{u} ψ) M N), ← cancel_mono (δ G M N)]
    simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc]
    -- The oplax comparison on the composite site uses the definitional presentation of
    -- inverse image as the composite of the two inverse-image functors.
    erw [hμδ, Category.comp_id]
    exact hδ M N

end Coherence

end

end TauCeti.SheafOfModules
