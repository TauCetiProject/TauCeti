/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Pullback
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Pushforward

/-!
# The exterior-power pullback comparison for sheaves of modules

Let `F : C ⥤ D` be a continuous functor between small sites, `S` and `R` sheaves of commutative
rings on `C` and `D`, and `φ : S ⟶ F_* R` a morphism of the underlying sheaves of rings. This
file constructs the canonical natural maps

* `TauCeti.SheafOfModules.pushforwardExteriorPowerComparison φ n : ⋀ⁿ (φ_* M) ⟶ φ_* (⋀ⁿ M)`,
  the sheafification of the sectionwise comparison
  `TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison`, which sends a wedge to the
  same wedge balanced over the target ring;
* `TauCeti.SheafOfModules.pullbackExteriorPowerComparison φ n : φ^* (⋀ⁿ M) ⟶ ⋀ⁿ (φ^* M)`, its
  mate under the pullback--pushforward adjunction.

These are the maps whose invertibility expresses the compatibility of exterior powers with
pullback. Both are characterized by their transposes
(`unit_comp_val_pushforwardExteriorPowerComparison_app` and
`unit_comp_pushforward_map_pullbackExteriorPowerComparison_app`). In degree one both are the
identity, read through `⋀¹ M ≅ M`, so the pullback comparison is an isomorphism in degree one
(`isIso_pullbackExteriorPowerComparison_one`); no invertibility is asserted in other degrees.
For a morphism of schemes `f`, these apply with `φ = f.toRingCatSheafHom`; the scheme case is
packaged as `AlgebraicGeometry.Scheme.Modules.pullbackExteriorPowerComparison`.

The pullback comparison is built as the oplax tensor comparison of pullback is in
`TauCeti.SheafOfModules.pullbackOplaxMonoidal`: as the mate of a lax comparison of pushforward.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.16.
-/

public section

open CategoryTheory

namespace TauCeti.SheafOfModules

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {F : C ⥤ D} [F.IsContinuous J K] {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))

/-- The underlying map of presheaves of the exterior-power comparison of pushforward: the
sectionwise comparison followed by the pushforward of the sheafification map of `⋀ⁿ M`. -/
private def presheafComparisonApp (n : ℕ) (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (PresheafOfModulesOfCommRing.exteriorPower (R := S.obj) n).obj
        ((_root_.SheafOfModules.pushforward φ).obj M).val ⟶
      ((_root_.SheafOfModules.pushforward φ).obj
        ((_root_.SheafOfModules.exteriorPower R n).obj M)).val :=
  (TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison (commRingCatHom φ) n).app M.val ≫
    (presheafPushforward φ).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj M.val) ≫
        (_root_.SheafOfModules.exteriorPowerIso n M).inv.val)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- `presheafComparisonApp` is natural in the sheaf of modules. -/
private lemma presheafComparisonApp_naturality (n : ℕ)
    {M N : _root_.SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ N) :
    (PresheafOfModulesOfCommRing.exteriorPower (R := S.obj) n).map
        ((_root_.SheafOfModules.pushforward φ).map f).val ≫ presheafComparisonApp φ n N =
      presheafComparisonApp φ n M ≫
        ((_root_.SheafOfModules.pushforward φ).map
          ((_root_.SheafOfModules.exteriorPower R n).map f)).val := by
  -- The sectionwise comparison is natural, and so is the sheafification map of `⋀ⁿ`.
  have h₁ : (PresheafOfModulesOfCommRing.exteriorPower (R := S.obj) n).map
        ((_root_.SheafOfModules.pushforward φ).map f).val ≫
      (TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison (commRingCatHom φ) n).app
        N.val =
      (TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison (commRingCatHom φ) n).app
          M.val ≫
        (presheafPushforward φ).map
          ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).map f.val) :=
    (TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison
      (commRingCatHom φ) n).naturality f.val
  have h₂ : (PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).map f.val ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj N.val) ≫
        (_root_.SheafOfModules.exteriorPowerIso n N).inv.val =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
          ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj M.val) ≫
        (_root_.SheafOfModules.exteriorPowerIso n M).inv.val) ≫
          ((_root_.SheafOfModules.exteriorPower R n).map f).val := by
    have e : (_root_.SheafOfModules.exteriorPowerIso n M).inv ≫
        (_root_.SheafOfModules.exteriorPower R n).map f =
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).map f.val) ≫
          (_root_.SheafOfModules.exteriorPowerIso n N).inv := by
      rw [_root_.SheafOfModules.exteriorPower_map, Iso.inv_hom_id_assoc]
    exact ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringCatSheaf R).obj)).unit.naturality_assoc _ _).trans
        ((congrArg (_ ≫ ·) (congrArg (·.val) e).symm).trans (Category.assoc _ _ _).symm)
  unfold presheafComparisonApp
  -- The rewrites are applied as terms: the two descriptions of the coefficient rings,
  -- `(ringCatSheaf S).obj` and `S.obj ⋙ forget₂ _ _`, agree only up to unfolding.
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (((presheafPushforward φ).map_comp _ _).symm.trans
        ((congrArg (presheafPushforward φ).map h₂).trans
          ((presheafPushforward φ).map_comp _ _)))).trans (Category.assoc _ _ _).symm)))

/-- Pushforward of sheaves of modules carries the canonical exterior-power comparison
`⋀ⁿ (φ_* M) ⟶ φ_* (⋀ⁿ M)`. -/
def pushforwardExteriorPowerComparison (n : ℕ) :
    _root_.SheafOfModules.pushforward φ ⋙ _root_.SheafOfModules.exteriorPower S n ⟶
      _root_.SheafOfModules.exteriorPower R n ⋙ _root_.SheafOfModules.pushforward φ where
  app M := (_root_.SheafOfModules.exteriorPowerIso n _).hom ≫
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).homEquiv _ _).symm
      (presheafComparisonApp φ n M)
  naturality M N f := by
    rw [Functor.comp_map, _root_.SheafOfModules.exteriorPower_map, Category.assoc, Category.assoc,
      Iso.inv_hom_id_assoc]
    exact (congrArg (_ ≫ ·) (((Adjunction.homEquiv_naturality_left_symm _ _ _).symm.trans
      (congrArg _ (presheafComparisonApp_naturality φ n f))).trans
        (Adjunction.homEquiv_naturality_right_symm _ _ _))).trans (Category.assoc _ _ _).symm

/-- The exterior-power comparison of pushforward is the sheafification of the sectionwise
comparison: on the sheafification map of the sectionwise exterior power of `φ_* M`, it is the
sectionwise comparison followed by the pushforward of the sheafification map of `⋀ⁿ M`. -/
theorem unit_comp_val_pushforwardExteriorPowerComparison_app (n : ℕ)
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).unit.app
        ((PresheafOfModulesOfCommRing.exteriorPower (R := S.obj) n).obj
          ((_root_.SheafOfModules.pushforward φ).obj M).val) ≫
      ((_root_.SheafOfModules.exteriorPowerIso n _).inv ≫
        (pushforwardExteriorPowerComparison φ n).app M).val =
    (TauCeti.PresheafOfModules.pushforwardExteriorPowerComparison (commRingCatHom φ) n).app M.val ≫
      (presheafPushforward φ).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
            ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj M.val) ≫
          (_root_.SheafOfModules.exteriorPowerIso n M).inv.val) := by
  have := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).homEquiv_unit
    _ _ (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).homEquiv _
      ((_root_.SheafOfModules.pushforward φ).obj
        ((_root_.SheafOfModules.exteriorPower R n).obj M))).symm (presheafComparisonApp φ n M))
  dsimp only [pushforwardExteriorPowerComparison]
  rw [Iso.inv_hom_id_assoc]
  exact this.symm.trans (Equiv.apply_symm_apply _ _)

/-- In degree one, the exterior-power comparison of pushforward is the identity of `φ_* M`, read
through the identifications `⋀¹ M ≅ M`. -/
-- Not `@[simp]`: `exteriorPowerOneIso_hom_app` unfolds the left-hand side.
@[reassoc]
theorem pushforwardExteriorPowerComparison_app_comp_map_exteriorPowerOneIso
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardExteriorPowerComparison φ 1).app M ≫
        (_root_.SheafOfModules.pushforward φ).map
          ((_root_.SheafOfModules.exteriorPowerOneIso R).hom.app M) =
      (_root_.SheafOfModules.exteriorPowerOneIso S).hom.app
        ((_root_.SheafOfModules.pushforward φ).obj M) := by
  rw [← cancel_epi (_root_.SheafOfModules.exteriorPowerIso 1
    ((_root_.SheafOfModules.pushforward φ).obj M)).inv]
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringCatSheaf S).obj)).homEquiv _ _).injective
  -- Compare the transposes along the sheafification map of `⋀¹ (φ_* M)`: both are the
  -- sectionwise identification `⋀¹ (φ_* M) ≅ φ_* M`.
  have key : (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).unit.app
        ((PresheafOfModulesOfCommRing.exteriorPower (R := S.obj) 1).obj
          ((_root_.SheafOfModules.pushforward φ).obj M).val) ≫
      ((_root_.SheafOfModules.exteriorPowerIso 1 _).inv ≫
          (pushforwardExteriorPowerComparison φ 1).app M).val ≫
        ((_root_.SheafOfModules.pushforward φ).map
          ((_root_.SheafOfModules.exteriorPowerOneIso R).hom.app M)).val =
      (PresheafOfModulesOfCommRing.exteriorPowerOneIso S.obj).hom.app
        ((_root_.SheafOfModules.pushforward φ).obj M).val :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (unit_comp_val_pushforwardExteriorPowerComparison_app φ 1 M)).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
          (((presheafPushforward φ).map_comp _ _).symm.trans
            (congrArg (presheafPushforward φ).map ((Category.assoc _ _ _).trans
              (_root_.SheafOfModules.unit_comp_val_exteriorPowerOneIso_hom_app M))))).trans
          (PresheafOfModules.pushforwardExteriorPowerComparison_app_comp_map_exteriorPowerOneIso
            (commRingCatHom φ) M.val))))
  exact (Adjunction.homEquiv_unit _ _ _ _).trans ((key.trans
    (_root_.SheafOfModules.unit_comp_val_exteriorPowerOneIso_hom_app
      ((_root_.SheafOfModules.pushforward φ).obj M)).symm).trans
      (Adjunction.homEquiv_unit
        (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)) _ _
        ((_root_.SheafOfModules.exteriorPowerIso 1 _).inv ≫
          (_root_.SheafOfModules.exteriorPowerOneIso S).hom.app
            ((_root_.SheafOfModules.pushforward φ).obj M))).symm)

variable [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- The canonical comparison `φ^* (⋀ⁿ M) ⟶ ⋀ⁿ (φ^* M)` between the pullback of an exterior power
of a sheaf of modules and the exterior power of its pullback: the mate of
`pushforwardExteriorPowerComparison` under the pullback--pushforward adjunction. -/
def pullbackExteriorPowerComparison (n : ℕ) :
    _root_.SheafOfModules.exteriorPower S n ⋙ _root_.SheafOfModules.pullback φ ⟶
      _root_.SheafOfModules.pullback φ ⋙ _root_.SheafOfModules.exteriorPower R n :=
  let A := _root_.SheafOfModules.pullbackPushforwardAdjunction φ
  ((mateEquiv A A).symm (TwoSquare.mk _ _ _ _ (pushforwardExteriorPowerComparison φ n))).natTrans

/-- The adjunction equation characterizing the pullback comparison: its transpose is the
exterior power of the unit `M ⟶ φ_* φ^* M` followed by the pushforward comparison. -/
@[reassoc (attr := simp)]
theorem unit_comp_pushforward_map_pullbackExteriorPowerComparison_app (n : ℕ)
    (M : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    (_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app
        ((_root_.SheafOfModules.exteriorPower S n).obj M) ≫
      (_root_.SheafOfModules.pushforward φ).map ((pullbackExteriorPowerComparison φ n).app M) =
    (_root_.SheafOfModules.exteriorPower S n).map
        ((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.app M) ≫
      (pushforwardExteriorPowerComparison φ n).app ((_root_.SheafOfModules.pullback φ).obj M) :=
  (unit_mateEquiv_symm (_root_.SheafOfModules.pullbackPushforwardAdjunction φ)
    (_root_.SheafOfModules.pullbackPushforwardAdjunction φ)
    (TwoSquare.mk _ _ _ _ (pushforwardExteriorPowerComparison φ n)) M).symm

/-- In degree one, the pullback comparison is the identity of `φ^* M`, read through the
identifications `⋀¹ M ≅ M`. In particular it is an isomorphism in degree one. -/
-- Not `@[simp]`: `exteriorPowerOneIso_hom_app` unfolds the left-hand side.
@[reassoc]
theorem pullbackExteriorPowerComparison_app_comp_exteriorPowerOneIso
    (M : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    (pullbackExteriorPowerComparison φ 1).app M ≫
        (_root_.SheafOfModules.exteriorPowerOneIso R).hom.app
          ((_root_.SheafOfModules.pullback φ).obj M) =
      (_root_.SheafOfModules.pullback φ).map
        ((_root_.SheafOfModules.exteriorPowerOneIso S).hom.app M) := by
  apply ((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    unit_comp_pushforward_map_pullbackExteriorPowerComparison_app_assoc,
    pushforwardExteriorPowerComparison_app_comp_map_exteriorPowerOneIso]
  exact ((_root_.SheafOfModules.exteriorPowerOneIso S).hom.naturality _).trans
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction φ).unit.naturality _)

/-- The pullback comparison is an isomorphism in degree one. -/
instance isIso_pullbackExteriorPowerComparison_one :
    IsIso (pullbackExteriorPowerComparison φ 1) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [(Iso.eq_comp_inv ((_root_.SheafOfModules.exteriorPowerOneIso R).app _)).mpr
    (pullbackExteriorPowerComparison_app_comp_exteriorPowerOneIso φ M)]
  infer_instance

end

end TauCeti.SheafOfModules
