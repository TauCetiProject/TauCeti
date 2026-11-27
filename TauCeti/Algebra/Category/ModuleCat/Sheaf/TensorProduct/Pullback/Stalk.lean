/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pushforward
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Stalk

/-!
# Strong symmetric monoidal pullback

For an arbitrary morphism of ringed spaces, the canonical oplax tensor comparison for pullback
of sheaves of modules is an isomorphism (Stacks Project, Tag 01CD, the ringed-space form of
Tag 03EL for ringed topoi). On stalks the comparison is the standard equivalence distributing
extension of scalars over tensor products.

The inverse tensor and unit comparisons make pullback strong symmetric monoidal. Composition
coherence for these structures is developed in `Pullback/Composition.lean`.

* `SheafOfModules.pullback_δ_stalk` computes the linear stalk map of the tensor comparison.
* `SheafOfModules.isIso_pullback_δ` and `SheafOfModules.pullbackBraided` give invertibility
  of the comparison and the strong symmetric monoidal structure.
-/

public section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace TauCeti.SheafOfModules

noncomputable section

variable {X Y : TopCat.{u}} {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} {f : Y ⟶ X}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]
  (M N : _root_.SheafOfModules.{u} (ringCatSheaf 𝒪X))

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
  -- Germs use `.val.presheaf.obj`, while the section equation uses `.val.obj`;
  -- `erw` unfolds `PresheafOfModules.presheaf` and the `pullbackUnitApp` abbreviation.
  erw [_root_.SheafOfModules.pullback_δ_app_unit_tmul φ M N (op U) m n]
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
    tensorStalkEquivMonoidal_symm_tmul_germ 𝒪X M N (f y) U hy m n
  rw [hα]
  refine (congrArg d (pullbackStalkEquiv_tmul_germ φ (M ⊗ N) y a U hy
    ((Functor.LaxMonoidal.μ (_root_.SheafOfModules.forget (ringCatSheaf 𝒪X)) M N).app
      (op U) (m ⊗ₜ[𝒪X.obj.obj (op U)] n)))).trans ?_
  apply β.injective
  refine Eq.trans ?_ (β.apply_symm_apply _).symm
  refine (pullback_δ_stalk_germ φ M N y a U hy m n).trans ?_
  dsimp only [b, c]
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  -- The tensor factors use `.val.presheaf.obj`, while the pullback germ equations use
  -- `.val.obj`; `erw` unfolds `PresheafOfModules.presheaf` to identify these section types.
  erw [TensorProduct.congr_tmul, pullbackStalkEquiv_tmul_germ, pullbackStalkEquiv_tmul_germ]
  -- The scalar actions use the same stalk modules after unfolding the pullback section types.
  rw [one_smul, TensorProduct.smul_tmul']
  rfl

/-- On stalks, the tensor comparison for pullback acts by distributing scalar extension
over the tensor product, using the canonical pullback and tensor stalk equivalences. -/
theorem _root_.SheafOfModules.pullback_δ_stalk (y : Y) :
    letI := stalkAlgebra φ y
    (PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
      (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val).comp
        ((tensorStalkEquivMonoidal 𝒪X M N (f y)).symm.baseChange _ _ ≪≫ₗ
          pullbackStalkEquiv φ (M ⊗ N) y).toLinearMap =
      (TensorProduct.AlgebraTensorModule.distribBaseChange _ _ _ _ ≪≫ₗ
        TensorProduct.congr (pullbackStalkEquiv φ M y) (pullbackStalkEquiv φ N y) ≪≫ₗ
          (tensorStalkEquivMonoidal 𝒪Y ((_root_.SheafOfModules.pullback φ).obj M)
            ((_root_.SheafOfModules.pullback φ).obj N) y).symm).toLinearMap := by
  let := stalkAlgebra φ y
  -- Fold the canonical equivalence composites into the source and target used in the germ proof.
  change (PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
    (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val).comp
      (pullbackTensorStalkSource φ M N y).toLinearMap =
    (pullbackTensorStalkTarget φ M N y).toLinearMap
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

/-- The canonical tensor comparison for pullback of arbitrary sheaves of modules along a
morphism of ringed spaces is an isomorphism. -/
instance _root_.SheafOfModules.isIso_pullback_δ :
    IsIso (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N) := by
  suffices IsIso ((_root_.SheafOfModules.toSheaf (ringCatSheaf 𝒪Y)).map
      (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N)) by
    exact isIso_of_reflects_iso _ (_root_.SheafOfModules.toSheaf (ringCatSheaf 𝒪Y))
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  intro y
  -- Express the forgotten sheaf morphism through its underlying module presheaf.
  apply (PresheafOfModules.bijective_stalkMapCommRing_iff_isIso (S := 𝒪Y.obj) y
    (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val).mp
  let e := pullbackTensorStalkSource φ M N y
  have h : PresheafOfModules.stalkMapCommRing (S := 𝒪Y.obj) y
      (Functor.OplaxMonoidal.δ (_root_.SheafOfModules.pullback φ) M N).val =
        (pullbackTensorStalkEquiv φ M N y).toLinearMap := by
    apply (LinearMap.cancel_right e.surjective).mp
    exact (_root_.SheafOfModules.pullback_δ_stalk φ M N y).trans
      (e.symm_comp_cancel_right (pullbackTensorStalkTarget φ M N y).toLinearMap).symm
  rw [h]
  exact (pullbackTensorStalkEquiv φ M N y).bijective

/-- Pullback along a morphism of ringed spaces is strong symmetric monoidal, with its tensor
and unit maps inverse to the canonical oplax comparisons. -/
instance _root_.SheafOfModules.pullbackBraided :
    (_root_.SheafOfModules.pullback.{u} φ).Braided := by
  have : IsIso (Functor.OplaxMonoidal.η (_root_.SheafOfModules.pullback.{u} φ)) := by
    rw [_root_.SheafOfModules.pullback_η φ]
    infer_instance
  letI : (_root_.SheafOfModules.pullback.{u} φ).Monoidal :=
    Functor.Monoidal.ofOplaxMonoidal _
  exact (_root_.SheafOfModules.pullbackPushforwardAdjunction φ).leftAdjointBraided

/-- The unit comparison for strong monoidal pullback is the inverse of the canonical map
from the pullback of the structure sheaf to the structure sheaf. -/
@[simp]
theorem _root_.SheafOfModules.pullback_ε :
    Functor.LaxMonoidal.ε (_root_.SheafOfModules.pullback.{u} φ) =
      inv (_root_.SheafOfModules.pullbackObjUnitToUnit φ) := by
  simp only [← Functor.Monoidal.inv_η, _root_.SheafOfModules.pullback_η]

end

end TauCeti.SheafOfModules
