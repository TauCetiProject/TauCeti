/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Pullback

/-!
# Symmetric powers and pushforward along a left adjoint of sites

Let `F : C ⥤ D` be left adjoint to `G : D ⥤ C`, both continuous, and let `φ` and `ψ` be
compatible morphisms of sheaves of rings along `F` and `G`. Mathlib's
`SheafOfModules.pushforwardPushforwardAdj` makes the pushforward along `φ` left adjoint to the
pushforward along `ψ`. For the inclusion of an open subset `U` of a topological space, the
pushforward along `φ` is restriction to `U`.

This file shows that the unit `M ⟶ ψ_* φ_* M` of this adjunction is compatible with the canonical
symmetric-power comparisons `Symⁿ (φ_* M) ⟶ φ_* (Symⁿ M)` and `Symⁿ (ψ_* N) ⟶ ψ_* (Symⁿ N)` of
the two pushforwards: on sections both sides restrict symmetric tensors along the counit of
`F ⊣ G`. This is the symmetric-power analogue of
`TauCeti.SheafOfModules.pushforwardPushforwardAdj_unit_app_tensor`, and it is what identifies the
canonical symmetric-power comparison of a pullback along an open immersion with the inverse of
the restriction isomorphism.

## Main declaration

* `TauCeti.SheafOfModules.pushforwardPushforwardAdj_unit_app_symmetricPower`: the unit of the
  adjunction between pushforwards, evaluated on `Symⁿ M`, factors through the two
  symmetric-power comparisons.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.16.
-/

public section

open CategoryTheory

namespace TauCeti.SheafOfModules

universe u v₁ v₂ u₁ u₂

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C ⥤ D} {G : D ⥤ C} [F.IsContinuous J K] [G.IsContinuous K J] (adj : F ⊣ G)
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))
  (ψ : ringCatSheaf R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj (ringCatSheaf S))
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) (ringCatSheaf R).obj =
    ψ.hom ≫ G.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op adj.unit) (ringCatSheaf S).obj = 𝟙 (ringCatSheaf S).obj)

/-- The unit `Symⁿ M ⟶ ψ_* φ_* (Symⁿ M)` of the adjunction between pushforwards is the symmetric
power of the unit of `M`, followed by the symmetric-power comparisons of `ψ_*` and of `φ_*`. On
sections over `V` both sides restrict a symmetric tensor along the counit `F (G V) ⟶ V`. -/
theorem pushforwardPushforwardAdj_unit_app_symmetricPower (n : ℕ)
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app
        ((_root_.SheafOfModules.symmetricPower R n).obj M) =
      (_root_.SheafOfModules.symmetricPower R n).map
          ((_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M) ≫
        (pushforwardSymmetricPowerComparison ψ n).app
          ((_root_.SheafOfModules.pushforward φ).obj M) ≫
        (_root_.SheafOfModules.pushforward ψ).map
          ((pushforwardSymmetricPowerComparison φ n).app M) := by
  symm
  apply symmetricPower_hom_ext n M
  intro V x
  let η := (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit
  let ε := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
      ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj M.val) ≫
    (_root_.SheafOfModules.forget _).map (_root_.SheafOfModules.symmetricPowerIso n M).inv
  -- On sections over `V`, the unit of `Symⁿ M` is restriction along the counit `F (G V) ⟶ V`,
  -- which commutes with sheafifying the symmetric tensor `x`.
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply ε (adj.counit.app V.unop).op x)
  -- Evaluate `Symⁿ` of the unit of `M` and the two pushforward comparisons on `x`.
  refine (congrArg (((_root_.SheafOfModules.pushforward ψ).map
    ((pushforwardSymmetricPowerComparison φ n).app M)).val.app V)
      ((congrArg (((pushforwardSymmetricPowerComparison ψ n).app
        ((_root_.SheafOfModules.pushforward φ).obj M)).val.app V)
          (_root_.SheafOfModules.symmetricPower_map_val_app_unit n (η.app M) V x)).trans
        (pushforwardSymmetricPowerComparison_app_val_app_unit ψ n _ V _))).trans ?_
  refine (pushforwardSymmetricPowerComparison_app_val_app_unit φ n M (G.op.obj V) _).trans ?_
  -- Both sides now sheafify a symmetric tensor over `F (G V)`; compare the two tensors in the
  -- symmetric algebra.
  refine congrArg (fun y ↦ ε.app (F.op.obj (G.op.obj V)) y) (Subtype.ext ?_)
  refine (TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ n _).trans ?_
  refine (congrArg (SymmetricAlgebra.mapₛₗ _)
    ((TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ n _).trans
      (congrArg (SymmetricAlgebra.mapₛₗ _)
        (ModuleCat.symmetricPower.coe_map_apply_eq_mapₛₗ _ n x)))).trans ?_
  refine Eq.trans ?_ (PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply n M.val
    (adj.counit.app V.unop).op x).symm
  -- The three maps of symmetric algebras compose to restriction along the counit: the first two
  -- combine on the nose, and the coefficient maps of the result compose to it by `H₁`. The
  -- coefficient ring is named because the unit's sections over `V` carry it under a different
  -- instance head.
  have hR := congrArg (fun α ↦ α.app V) H₁
  refine (congrArg (SymmetricAlgebra.mapₛₗ _) (RingHom.congr_fun
    (SymmetricAlgebra.mapₛₗ_comp_mapₛₗ (R := R.obj.obj V) _ _ (LinearMap.comp _ _)
      (fun _ ↦ rfl) (fun _ ↦ rfl)) _)).trans ?_
  exact RingHom.congr_fun (SymmetricAlgebra.mapₛₗ_comp_mapₛₗ (R := R.obj.obj V) _ _ _
    (fun r ↦ (ConcreteCategory.congr_hom hR r).symm) (fun _ ↦ rfl)) _

end

end TauCeti.SheafOfModules
