/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.InternalHom.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pullback.Stalk
public import TauCeti.CategoryTheory.Monoidal.Closed.Functor

/-!
# Stalks of the pullback comparison for internal Hom

For a morphism of ringed spaces, the canonical pullback comparison
`CategoryTheory.Functor.ihomComparison` for internal Hom
commutes, on stalks, with the linear-map base change map. The vertical maps are
`SheafOfModules.ihomStalkComparison` and its scalar extension, using
`TauCeti.SheafOfModules.pullbackStalkEquiv` to identify stalks of pullbacks.
This is the comparison square used in the stalk proof of flat base change
(Stacks Project, Tag 0C6I). The square itself applies to arbitrary module sheaves
and arbitrary morphisms of ringed spaces.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite TopologicalSpace
open scoped TensorProduct
open TauCeti.SheafOfModules

universe u

namespace SheafOfModules

noncomputable section

variable {X Y : TopCat.{u}} {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} {f : Y ⟶ X}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  [(pushforward.{u} φ).IsRightAdjoint]
  (M N : SheafOfModules.{u} (ringCatSheaf 𝒪X))

/-- Evaluating the pulled-back local morphism on a pulled-back section gives the pullback of
its original value. Both pullbacks of sections use the unit of the module pullback adjunction. -/
private theorem pullback_ihomComparison_eval (U : Opens X) (m : M.val.obj (op U))
    (s : ((ihom M).obj N).val.obj (op U)) :
    let F := pullback φ
    let c := (F.ihomComparison M).app N
    ((F.obj M).ihomObjEquiv (F.obj N) ((Opens.map f).obj U)
      (c.val.app (op ((Opens.map f).obj U)) (pullbackUnitApp φ ((ihom M).obj N) U s))).val.app
        (op (Over.mk (𝟙 ((Opens.map f).obj U)))) (pullbackUnitApp φ M U m) =
      pullbackUnitApp φ N U ((M.ihomObjEquiv N U s).val.app (op (Over.mk (𝟙 U))) m) := by
  dsimp only
  let F := pullback φ
  let H := (ihom M).obj N
  let c := (F.ihomComparison M).app N
  let V := (Opens.map f).obj U
  let ev := (ihom.ev M).app N
  let ev' := (ihom.ev (F.obj M)).app (F.obj N)
  let δ := Functor.OplaxMonoidal.δ F M H
  let q := (Functor.LaxMonoidal.μ (forget (ringCatSheaf 𝒪X)) M H).app
    (op U) (m ⊗ₜ[𝒪X.obj.obj (op U)] s)
  have h := Functor.ihomComparison_ev F M N
  have he : δ ≫ F.obj M ◁ c ≫ ev' = F.map ev := by
    rw [h, Functor.Monoidal.δ_μ_assoc]
  have hd := pullback_δ_app_unit_tmul φ M H (op U) m s
  have hn := (pullbackPushforwardAdjunction φ).unit.naturality ev
  have hw := Functor.LaxMonoidal.μ_natural_right (forget (ringCatSheaf 𝒪Y)) (F.obj M) c
  -- Compare the evaluations on the tensor of the two unit images.
  let m' := pullbackUnitApp φ M U m
  let s' := pullbackUnitApp φ H U s
  erw [← ihom_ev_app_tmul (F.obj M) (F.obj N) V m' (c.val.app (op V) s'),
    ← ihom_ev_app_tmul M N U m s]
  have hwV := congrArg (fun k ↦ k.app (op V)) hw
  simp only [PresheafOfModules.comp_app] at hwV
  have ht : ((F.obj M).val ◁ c.val).app (op V) (m' ⊗ₜ[𝒪Y.obj.obj (op V)] s') =
      m' ⊗ₜ[𝒪Y.obj.obj (op V)] c.val.app (op V) s' :=
    ModuleCat.MonoidalCategory.whiskerLeft_apply (R := 𝒪Y.obj.obj (op V))
      ((F.obj M).val.obj (op V)) (c.val.app (op V)) m' s'
  have hwhisker := congrArg (fun k ↦ k (m' ⊗ₜ[𝒪Y.obj.obj (op V)] s')) hwV
  have hmap := congrArg (fun k ↦ k.val.app (op V) (pullbackUnitApp φ (M ⊗ H) U q)) he
  refine (congrArg (ev'.val.app (op V) ∘
    (Functor.LaxMonoidal.μ (forget (ringCatSheaf 𝒪Y)) (F.obj M)
      ((ihom (F.obj M)).obj (F.obj N))).app (op V)) ht.symm).trans ?_
  exact (congrArg (ev'.val.app (op V)) hwhisker).trans
    ((congrArg (fun t ↦ ev'.val.app (op V) ((F.obj M ◁ c).val.app (op V) t)) hd.symm).trans
      (hmap.trans (congrArg (fun k ↦ k.val.app (op U) q) hn).symm))

/-- The pullback comparison on stalks, evaluated on the images of two tensors with scalar
coefficient one, is the image of the original stalk evaluation. -/
private theorem pullback_ihomComparison_stalk_one_tmul (y : Y)
    (s : ↑(TopCat.Presheaf.stalk ((ihom M).obj N).val.presheaf (f y)))
    (m : ↑(TopCat.Presheaf.stalk M.val.presheaf (f y))) :
    letI := stalkAlgebra φ y
    let F := pullback φ
    let H := (ihom M).obj N
    let c := (F.ihomComparison M).app N
    (F.obj M).ihomStalkComparison (F.obj N) y
        (PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y c.val
          (pullbackStalkEquiv φ H y (1 ⊗ₜ s))) (pullbackStalkEquiv φ M y (1 ⊗ₜ m)) =
      pullbackStalkEquiv φ N y (1 ⊗ₜ M.ihomStalkComparison N (f y) s m) := by
  let := stalkAlgebra φ y
  dsimp only
  let F := pullback φ
  let H := (ihom M).obj N
  obtain ⟨U, hy, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq H.val.presheaf s
  obtain ⟨V, hVU, hyV, m, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq M.val.presheaf m hy
  rw [← TopCat.Presheaf.germ_res_apply H.val.presheaf (homOfLE hVU) (f y) hyV s]
  let sV : H.val.obj (op V) := H.val.map (homOfLE hVU).op s
  -- Both germs now have representatives on the same open. The germ lemmas identify section
  -- types written using the underlying presheaf with the bundled module sections.
  erw [pullbackStalkEquiv_tmul_germ φ H y 1 V hyV sV,
    pullbackStalkEquiv_tmul_germ φ M y 1 V hyV m]
  simp only [one_smul]
  erw [PresheafOfModules.stalkMapCommRing_germ (S := 𝒪Y.obj),
    ihomStalkComparison_germ_apply _ _ y _ hyV _ _ (𝟙 _) hyV,
    ihomStalkComparison_germ_apply M N (f y) V hyV sV V (𝟙 V) hyV,
    pullbackStalkEquiv_tmul_germ φ N y 1 V hyV]
  simp only [one_smul]
  exact congrArg (TopCat.Presheaf.germ (F.obj N).val.presheaf _ y hyV)
    (pullback_ihomComparison_eval φ M N V m sV)

/-- On stalks, the internal-Hom comparison of module pullback commutes with extension of
scalars of linear maps. The left side pulls back the internal Hom, takes the stalk map of
the comparison, then lets the resulting germ act on stalks. The right side first lets the
original germ act on stalks, then extends scalars on the resulting linear map. -/
theorem pullback_ihomComparison_stalk (y : Y) :
    letI := stalkAlgebra φ y
    let F := pullback φ
    let H := (ihom M).obj N
    let c := (F.ihomComparison M).app N
    ((pullbackStalkEquiv φ M y).arrowCongr (pullbackStalkEquiv φ N y)).symm.toLinearMap ∘ₗ
        (F.obj M).ihomStalkComparison (F.obj N) y ∘ₗ
        PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y c.val ∘ₗ
        (pullbackStalkEquiv φ H y).toLinearMap =
      ((LinearMap.baseChangeHom _ ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) _ _).comp
        (M.ihomStalkComparison N (f y))).liftBaseChange ↑(TopCat.Presheaf.stalk 𝒪Y.obj y) := by
  let := stalkAlgebra φ y
  dsimp only
  -- Linearity in each tensor argument reduces to coefficient one.
  -- The linearity rewrites identify the scalar actions written using the sheaf and its presheaf.
  apply TensorProduct.AlgebraTensorModule.ext
  intro a s
  erw [TensorProduct.tmul_eq_smul_one_tmul a s, map_smul, map_smul]
  apply congrArg (a • ·)
  apply TensorProduct.AlgebraTensorModule.ext
  intro b m
  erw [TensorProduct.tmul_eq_smul_one_tmul b m, map_smul, map_smul]
  apply congrArg (b • ·)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.arrowCongr_symm_apply]
  erw [LinearMap.liftBaseChange_one_tmul, LinearMap.comp_apply, LinearMap.baseChangeHom_apply,
    LinearMap.baseChange_tmul]
  exact (pullbackStalkEquiv φ N y).symm_apply_eq.mpr
    (pullback_ihomComparison_stalk_one_tmul φ M N y s m)

end

end SheafOfModules
