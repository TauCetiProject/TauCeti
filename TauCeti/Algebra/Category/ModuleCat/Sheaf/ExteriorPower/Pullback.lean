/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Pullback
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pushforward.Comparison

/-!
# The exterior-power pullback comparison for sheaves of modules

Let `F : C ⥤ D` be a continuous functor between sites, `S` and `R` sheaves of commutative
rings on `C` and `D`, and `φ : S ⟶ F_* R` a morphism of the underlying sheaves of rings. This file
constructs the canonical natural map `⋀ⁿ (φ_* M) ⟶ φ_* (⋀ⁿ M)` for sheaves of `R`-modules `M`.
It is the sheafification of the sectionwise comparison
`TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison`, which changes the coefficient ring
of a wedge without changing its factors, followed by the unit of sheafification of `⋀ⁿ M`.

Its mate under an adjunction `G ⊣ φ_*` is the canonical natural map `G (⋀ⁿ M) ⟶ ⋀ⁿ (G M)`. The
adjunction is an explicit argument, so that the comparison `f^* (⋀ⁿ M) ⟶ ⋀ⁿ (f^* M)` is available
for each model of pullback: `SheafOfModules.pullbackPushforwardAdjunction φ` gives it for
`SheafOfModules.pullback φ`, and, for a morphism of schemes `f`,
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f` gives it for
`AlgebraicGeometry.Scheme.Modules.pullback f`. Both maps are characterized on sheafified wedges
of sections. In degree one the comparison is an isomorphism, for every such adjunction.

## Main declarations

* `SheafOfModules.pushforwardExteriorPowerComparison φ n`: the natural map
  `⋀ⁿ (φ_* M) ⟶ φ_* (⋀ⁿ M)`, determined on underlying presheaves by
  `unit_comp_forget_map_pushforwardExteriorPowerComparison_app` and computed on sheafified wedges
  by `pushforwardExteriorPowerComparison_app_val_app_mk`;
* `SheafOfModules.pullbackExteriorPowerComparison adj n`: the natural map
  `G (⋀ⁿ M) ⟶ ⋀ⁿ (G M)` for a left adjoint `G` of `φ_*`, characterized by the adjunction equation
  `unit_comp_pushforward_pullbackExteriorPowerComparison` and computed on the unit images of
  sheafified wedges by `pullbackExteriorPowerComparison_app_val_app_unit_mk`.

The construction transfers the presheaf-level comparisons of
`TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Pullback` to sheaves by the general
sheafification `TauCeti.SheafOfModules.sheafifyPushforwardComparison` of sectionwise pushforward
comparisons, which uses the pushforward of underlying presheaves
`TauCeti.SheafOfModules.presheafPushforward` as in the lax monoidal structure of
`TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pushforward`.

When the coefficient map is an isomorphism and the site functor is also cocontinuous, the
pushforward comparison is invertible.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.16.
-/

public section

open CategoryTheory
open TauCeti.SheafOfModules (commRingCatHom presheafPushforward ringCatSheaf
  sheafifyPushforwardComparison sheafifyPushforwardComparison_app_comp_pushforward_map
  unit_comp_forget_map_sheafifyPushforwardComparison_app)

namespace SheafOfModules

universe u v₁ v₂ u₁ u₂

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C ⥤ D} [F.IsContinuous J K] {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))

/-- The canonical natural map `⋀ⁿ (φ_* M) ⟶ φ_* (⋀ⁿ M)`: the sheafification
`sheafifyPushforwardComparison` of the sectionwise exterior-power comparison. On sections it sends
the sheafified wedge of sections of `M` to their sheafified wedge over the target coefficient ring
(`pushforwardExteriorPowerComparison_app_val_app_mk`). -/
def pushforwardExteriorPowerComparison (n : ℕ) :
    pushforward φ ⋙ exteriorPower S n ⟶ exteriorPower R n ⋙ pushforward φ :=
  sheafifyPushforwardComparison φ (exteriorPowerIso n) (exteriorPower_map n)
    (exteriorPowerIso n) (exteriorPower_map n)
    (TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison (commRingCatHom φ) n)

/-- On underlying presheaves, the pushforward comparison restricted along the sheafification unit
is the sectionwise comparison followed by the pushforward of the sheafification unit of `⋀ⁿ M`.
This determines the comparison, by the universal property of sheafification. -/
@[reassoc]
theorem unit_comp_forget_map_pushforwardExteriorPowerComparison_app (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).unit.app
        ((PresheafOfModulesOfCommRing.exteriorPower (R := S.obj) n).obj
          ((pushforward φ).obj M).val) ≫
      (SheafOfModules.forget _).map
        ((exteriorPowerIso n ((pushforward φ).obj M)).inv ≫
          (pushforwardExteriorPowerComparison φ n).app M) =
    (TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison (commRingCatHom φ) n).app
        M.val ≫
      (presheafPushforward φ).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj M.val) ≫
          (SheafOfModules.forget _).map (exteriorPowerIso n M).inv) :=
  unit_comp_forget_map_sheafifyPushforwardComparison_app φ _ _ _ _ _ M

/-- On sections over `U`, the pushforward comparison sends the sheafified wedge `m₁ ∧ ⋯ ∧ mₙ` of
sections of `φ_* M` to the sheafified wedge of the same sections of `M` over `F U`, balanced over
the target coefficient ring. -/
@[simp]
theorem pushforwardExteriorPowerComparison_app_val_app_mk (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) (U : Cᵒᵖ)
    (m : Fin n → PresheafOfModulesOfCommRing.obj (R := S.obj) ((pushforward φ).obj M).val U) :
    dsimp% only [Functor.comp_obj, ObjectProperty.ι_obj]
    (((pushforwardExteriorPowerComparison φ n).app M).val.app U
      ((exteriorPowerIso n ((pushforward φ).obj M)).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower (R := S.obj) n).obj
            ((pushforward φ).obj M).val)).app U
          (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj (R := S.obj)
            ((pushforward φ).obj M).val U) m))) =
    (exteriorPowerIso n M).inv.val.app (F.op.obj U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj M.val)).app (F.op.obj U)
        (ModuleCat.exteriorPower.mk
          (M := PresheafOfModulesOfCommRing.obj (R := R.obj) M.val (F.op.obj U)) m))) := by
  have h := ConcreteCategory.congr_hom (congrArg (fun α ↦ α.app U)
    (unit_comp_forget_map_pushforwardExteriorPowerComparison_app φ n M))
    (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj (R := S.obj)
      ((pushforward φ).obj M).val U) m)
  -- Composites in `ModuleCat` and pushforwards of morphisms of presheaves of modules evaluate on
  -- sections by definition, so `h` is the goal after the sectionwise wedge formula.
  refine h.trans ?_
  exact congrArg (fun x ↦
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
      ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj M.val)) ≫
      (SheafOfModules.forget _).map (exteriorPowerIso n M).inv).app (F.op.obj U) x)
    (TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison_app_app_mk
      (commRingCatHom φ) n M.val U m)

/-- In degree one, the exterior-power comparison of pushforward is the identity of `φ_* M`, read
through the identifications `⋀¹ M ≅ M`. -/
-- Not `@[simp]`: `exteriorPowerOneIso_hom_app` unfolds the left-hand side.
@[reassoc]
theorem pushforwardExteriorPowerComparison_app_comp_map_exteriorPowerOneIso
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardExteriorPowerComparison φ 1).app M ≫
        (pushforward φ).map ((exteriorPowerOneIso R).hom.app M) =
      (exteriorPowerOneIso S).hom.app ((pushforward φ).obj M) :=
  sheafifyPushforwardComparison_app_comp_pushforward_map φ _ _ _ _ _ M
    (oS := (PresheafOfModulesOfCommRing.exteriorPowerOneIso S.obj).hom.app
      ((pushforward φ).obj M).val)
    (oR := (PresheafOfModulesOfCommRing.exteriorPowerOneIso R.obj).hom.app M.val)
    (by rw [exteriorPowerOneIso_hom_app, Iso.inv_hom_id_assoc])
    (by rw [exteriorPowerOneIso_hom_app, Iso.inv_hom_id_assoc]) <|
  TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison_app_comp_map_exteriorPowerOneIso
    (commRingCatHom φ) M.val

-- Adapted from `SheafOfModules.isIso_pushforwardSymmetricPowerComparison`.
/-- Restriction along a continuous and cocontinuous functor with an isomorphism of coefficient
sheaves preserves every exterior power. -/
instance isIso_pushforwardExteriorPowerComparison [F.IsCocontinuous J K] [IsIso φ] (n : ℕ) :
    IsIso (pushforwardExteriorPowerComparison φ n) := by
  have hα : IsIso (commRingCatHom φ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      ((ConcreteCategory.isIso_iff_bijective (φ.hom.app U)).mp inferInstance)
  unfold pushforwardExteriorPowerComparison
  infer_instance

variable {φ} {G : SheafOfModules.{u} (ringCatSheaf S) ⥤ SheafOfModules.{u} (ringCatSheaf R)}
  (adj : G ⊣ pushforward φ)

/-- The canonical natural map `G (⋀ⁿ M) ⟶ ⋀ⁿ (G M)` for a left adjoint `G` of the pushforward
`φ_*`, such as the pullback of sheaves of modules: the mate of
`pushforwardExteriorPowerComparison φ n` under `adj`. -/
def pullbackExteriorPowerComparison (n : ℕ) :
    exteriorPower S n ⋙ G ⟶ G ⋙ exteriorPower R n :=
  (mateEquiv adj adj).symm (pushforwardExteriorPowerComparison φ n)

/-- The mate of the exterior-power pullback comparison is the sectionwise pushforward
comparison. -/
-- Not a simp lemma: `mateEquiv_apply` expands its left-hand side first.
theorem mateEquiv_pullbackExteriorPowerComparison (n : ℕ) :
    mateEquiv adj adj (pullbackExteriorPowerComparison adj n) =
      pushforwardExteriorPowerComparison φ n :=
  Equiv.apply_symm_apply _ _

/-- The adjunction equation characterizing the pullback comparison. -/
@[reassoc (attr := simp)]
theorem unit_comp_pushforward_pullbackExteriorPowerComparison (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf S)) :
    adj.unit.app ((exteriorPower S n).obj M) ≫
      (pushforward φ).map ((pullbackExteriorPowerComparison adj n).app M) =
    (exteriorPower S n).map (adj.unit.app M) ≫
      (pushforwardExteriorPowerComparison φ n).app (G.obj M) :=
  (unit_mateEquiv_symm adj adj (TwoSquare.mk _ _ _ _ (pushforwardExteriorPowerComparison φ n))
    M).symm

/-- On a sheafified wedge in the image of the adjunction unit, the pullback comparison takes the
sheafified wedge of the images of its factors under the unit. -/
@[simp]
theorem pullbackExteriorPowerComparison_app_val_app_unit_mk (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf S)) (U : Cᵒᵖ)
    (m : Fin n → PresheafOfModulesOfCommRing.obj (R := S.obj) M.val U) :
    dsimp% only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj, Functor.op_obj]
    (((pullbackExteriorPowerComparison adj n).app M).val.app (F.op.obj U)
      ((adj.unit.app ((exteriorPower S n).obj M)).val.app U
        ((exteriorPowerIso n M).inv.val.app U
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).unit.app
            ((PresheafOfModulesOfCommRing.exteriorPower (R := S.obj) n).obj M.val)).app U
            (ModuleCat.exteriorPower.mk
              (M := PresheafOfModulesOfCommRing.obj (R := S.obj) M.val U) m)))) =
    (exteriorPowerIso n (G.obj M)).inv.val.app (F.op.obj U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj (G.obj M).val)).app
            (F.op.obj U)
        (ModuleCat.exteriorPower.mk
          (M := PresheafOfModulesOfCommRing.obj (R := R.obj) (G.obj M).val (F.op.obj U))
          (fun i ↦ (adj.unit.app M).val.app U (m i))))) := by
  have h := ConcreteCategory.congr_hom (congrArg (fun α ↦ α.val.app U)
    (unit_comp_pushforward_pullbackExteriorPowerComparison adj n M))
    ((exteriorPowerIso n M).inv.val.app U
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).unit.app
        ((PresheafOfModulesOfCommRing.exteriorPower (R := S.obj) n).obj M.val)).app U
        (ModuleCat.exteriorPower.mk
          (M := PresheafOfModulesOfCommRing.obj (R := S.obj) M.val U) m)))
  -- As in `pushforwardExteriorPowerComparison_app_val_app_mk`, composites evaluate on sections by
  -- definition; it remains to compute `⋀ⁿ` of the unit and the pushforward comparison on wedges.
  refine h.trans ?_
  refine (congrArg (((pushforwardExteriorPowerComparison φ n).app (G.obj M)).val.app U)
    (exteriorPower_map_val_app_mk n (adj.unit.app M) U m)).trans ?_
  exact pushforwardExteriorPowerComparison_app_val_app_mk φ n (G.obj M) U _

/-- In degree one, the pullback comparison is the identity of `φ^* M`, read through the
identifications `⋀¹ M ≅ M`. In particular it is an isomorphism in degree one. -/
-- Not `@[simp]`: `exteriorPowerOneIso_hom_app` unfolds the left-hand side.
@[reassoc]
theorem pullbackExteriorPowerComparison_app_comp_exteriorPowerOneIso
    (M : SheafOfModules.{u} (ringCatSheaf S)) :
    (pullbackExteriorPowerComparison adj 1).app M ≫
        (exteriorPowerOneIso R).hom.app (G.obj M) =
      G.map ((exteriorPowerOneIso S).hom.app M) := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    unit_comp_pushforward_pullbackExteriorPowerComparison_assoc,
    pushforwardExteriorPowerComparison_app_comp_map_exteriorPowerOneIso]
  exact ((exteriorPowerOneIso S).hom.naturality _).trans (adj.unit.naturality _)

/-- The pullback comparison is an isomorphism in degree one. -/
instance isIso_pullbackExteriorPowerComparison_one :
    IsIso (pullbackExteriorPowerComparison adj 1) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [(Iso.eq_comp_inv ((exteriorPowerOneIso R).app _)).mpr
    (pullbackExteriorPowerComparison_app_comp_exteriorPowerOneIso adj M)]
  infer_instance

end

end SheafOfModules
