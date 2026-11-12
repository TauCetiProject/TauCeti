/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Pullback

/-!
# Exterior powers and pushforward along a left adjoint of sites

Let `F : C ⥤ D` be left adjoint to `G : D ⥤ C`, both continuous, and let `φ` and `ψ` be
compatible morphisms of sheaves of rings along `F` and `G`. Mathlib's
`SheafOfModules.pushforwardPushforwardAdj` makes the pushforward along `φ` left adjoint to the
pushforward along `ψ`. For the inclusion of an open subset `U` of a topological space, the
pushforward along `φ` is restriction to `U`.

This file shows that the unit `M ⟶ ψ_* φ_* M` of this adjunction is compatible with the canonical
exterior-power comparisons `⋀ⁿ (φ_* M) ⟶ φ_* (⋀ⁿ M)` and `⋀ⁿ (ψ_* N) ⟶ ψ_* (⋀ⁿ N)` of the two
pushforwards: on sections both sides restrict each factor of a wedge along the counit of
`F ⊣ G`. This is the exterior-power analogue of
`TauCeti.SheafOfModules.pushforwardPushforwardAdj_unit_app_symmetricPower`, and it is what
identifies the canonical exterior-power comparison of a pullback along an open immersion with the
inverse of the restriction isomorphism.

## Main declaration

* `TauCeti.SheafOfModules.pushforwardPushforwardAdj_unit_app_exteriorPower`: the unit of the
  adjunction between pushforwards, evaluated on `⋀ⁿ M`, factors through the two exterior-power
  comparisons.

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

-- Adapted from `TauCeti.SheafOfModules.pushforwardPushforwardAdj_unit_app_symmetricPower`.
/-- The unit `⋀ⁿ M ⟶ ψ_* φ_* (⋀ⁿ M)` of the adjunction between pushforwards is the exterior
power of the unit of `M`, followed by the exterior-power comparisons of `ψ_*` and of `φ_*`. On
sections over `V` both sides restrict each factor of a wedge along the counit `F (G V) ⟶ V`. -/
theorem pushforwardPushforwardAdj_unit_app_exteriorPower (n : ℕ)
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app
        ((_root_.SheafOfModules.exteriorPower R n).obj M) =
      (_root_.SheafOfModules.exteriorPower R n).map
          ((_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M) ≫
        (pushforwardExteriorPowerComparison ψ n).app
          ((_root_.SheafOfModules.pushforward φ).obj M) ≫
        (_root_.SheafOfModules.pushforward ψ).map
          ((pushforwardExteriorPowerComparison φ n).app M) := by
  symm
  apply exteriorPower_hom_ext n M
  intro V m
  let η := (_root_.SheafOfModules.pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit
  let ε := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
      ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj M.val) ≫
    (_root_.SheafOfModules.forget _).map (_root_.SheafOfModules.exteriorPowerIso n M).inv
  -- On sections over `V`, the unit of `⋀ⁿ M` is restriction along the counit `F (G V) ⟶ V`,
  -- which commutes with sheafifying the wedge of `m`.
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply ε (adj.counit.app V.unop).op
    (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj (R := R.obj) M.val V) m))
  -- Evaluate `⋀ⁿ` of the unit of `M` and the two pushforward comparisons on the wedge.
  refine (congrArg (((_root_.SheafOfModules.pushforward ψ).map
    ((pushforwardExteriorPowerComparison φ n).app M)).val.app V)
      ((congrArg (((pushforwardExteriorPowerComparison ψ n).app
        ((_root_.SheafOfModules.pushforward φ).obj M)).val.app V)
          (_root_.SheafOfModules.exteriorPower_map_val_app_mk n (η.app M) V m)).trans
        (pushforwardExteriorPowerComparison_app_val_app_mk ψ n _ V _))).trans ?_
  refine (pushforwardExteriorPowerComparison_app_val_app_mk φ n M (G.op.obj V) _).trans ?_
  -- Both sides now sheafify a wedge over `F (G V)` whose factors are the restrictions of `m`.
  exact congrArg (fun y ↦ ε.app (F.op.obj (G.op.obj V)) y)
    (PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk n M.val
      (adj.counit.app V.unop).op m).symm

end

end TauCeti.SheafOfModules
