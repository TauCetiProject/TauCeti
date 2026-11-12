/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.SymmetricPower.Pullback
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pushforward.Comparison

/-!
# The symmetric-power pullback comparison for sheaves of modules

Let `F : C ⥤ D` be a continuous functor between sites, `S` and `R` sheaves of commutative
rings, and `φ : S ⟶ F_* R`. This file constructs the canonical natural map
`Symⁿ (φ_* M) ⟶ φ_* (Symⁿ M)`. It is the sheafification of the sectionwise comparison followed
by the unit of sheafification of `Symⁿ M`.

Its mate under an adjunction `G ⊣ φ_*` is the canonical natural map
`G (Symⁿ M) ⟶ Symⁿ (G M)`. The adjunction is an explicit argument, so the same construction
applies both to pullback of sheaves of modules and to pullback of modules on schemes. In degree
one the comparison is an isomorphism for every such adjunction. The pushforward comparison
is invertible in every degree when the functor of sites is also cocontinuous and the
coefficient-ring map is an isomorphism.

As for exterior powers in `TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Pullback`,
the pushforward comparison and its degree-one computation are instances of
`TauCeti.SheafOfModules.sheafifyPushforwardComparison`, applied to the symmetric-power comparison
of underlying presheaves.

## Main declarations

* `TauCeti.SheafOfModules.pushforwardSymmetricPowerComparison`: the canonical map
  `Symⁿ (φ_* M) ⟶ φ_* (Symⁿ M)`;
* `TauCeti.SheafOfModules.pullbackSymmetricPowerComparison`: its mate
  `G (Symⁿ M) ⟶ Symⁿ (G M)`;
* `TauCeti.SheafOfModules.pullbackSymmetricPowerComparison_app_val_app_unit`: its value on
  sheafified symmetric tensors in the image of the adjunction unit.

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
  {F : C ⥤ D} [F.IsContinuous J K] {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  (φ : ringCatSheaf S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj (ringCatSheaf R))

/-- The canonical natural map `Symⁿ (φ_* M) ⟶ φ_* (Symⁿ M)`: the sheafification
`sheafifyPushforwardComparison` of the sectionwise symmetric-power comparison. -/
def pushforwardSymmetricPowerComparison (n : ℕ) :
    _root_.SheafOfModules.pushforward φ ⋙ _root_.SheafOfModules.symmetricPower S n ⟶
      _root_.SheafOfModules.symmetricPower R n ⋙ _root_.SheafOfModules.pushforward φ :=
  sheafifyPushforwardComparison φ (_root_.SheafOfModules.symmetricPowerIso n)
    (_root_.SheafOfModules.symmetricPower_map n) (_root_.SheafOfModules.symmetricPowerIso n)
    (_root_.SheafOfModules.symmetricPower_map n)
    (PresheafOfModules.pushforwardSymmetricPowerComparison (commRingCatHom φ) n)

/-- On underlying presheaves, the pushforward comparison restricted along the sheafification
unit is the sectionwise comparison followed by the pushed-forward sheafification unit. This
equation uniquely determines the comparison. -/
@[reassoc]
theorem unit_comp_forget_map_pushforwardSymmetricPowerComparison_app (n : ℕ)
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower (R := S.obj) n).obj
          ((_root_.SheafOfModules.pushforward φ).obj M).val) ≫
      (_root_.SheafOfModules.forget _).map
        ((_root_.SheafOfModules.symmetricPowerIso n
            ((_root_.SheafOfModules.pushforward φ).obj M)).inv ≫
          (pushforwardSymmetricPowerComparison φ n).app M) =
    (PresheafOfModules.pushforwardSymmetricPowerComparison (commRingCatHom φ) n).app M.val ≫
      (presheafPushforward φ).map
        ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
          ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj M.val) ≫
          (_root_.SheafOfModules.forget _).map
            (_root_.SheafOfModules.symmetricPowerIso n M).inv) :=
  unit_comp_forget_map_sheafifyPushforwardComparison_app φ _ _ _ _ _ M

/-- On sections over `U`, the pushforward comparison sends the sheafification of a sectionwise
symmetric tensor `x` of `φ_* M` to the sheafification of the same symmetric tensor of `M` over
`F U`, with its coefficients mapped along `φ`. -/
@[simp]
theorem pushforwardSymmetricPowerComparison_app_val_app_unit (n : ℕ)
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) (U : Cᵒᵖ)
    (x : (PresheafOfModulesOfCommRing.obj (R := S.obj)
      ((_root_.SheafOfModules.pushforward φ).obj M).val U).symmetricPower n) :
    dsimp% only [Functor.comp_obj, ObjectProperty.ι_obj]
    (((pushforwardSymmetricPowerComparison φ n).app M).val.app U
      ((_root_.SheafOfModules.symmetricPowerIso n
          ((_root_.SheafOfModules.pushforward φ).obj M)).inv.val.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).unit.app
          ((PresheafOfModulesOfCommRing.symmetricPower (R := S.obj) n).obj
            ((_root_.SheafOfModules.pushforward φ).obj M).val)).app U x)) =
    (_root_.SheafOfModules.symmetricPowerIso n M).inv.val.app (F.op.obj U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
          ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj M.val)).app (F.op.obj U)
        (TauCeti.SymmetricAlgebra.homogeneousSubmoduleMapₛₗ
          ((_root_.ModuleCat.semilinearMapAddEquiv ((commRingCatHom φ).app U).hom
            ((ModuleCat.restrictScalars ((commRingCatHom φ).app U).hom).obj
              (PresheafOfModulesOfCommRing.obj (R := R.obj) M.val (F.op.obj U)))
            (PresheafOfModulesOfCommRing.obj (R := R.obj) M.val (F.op.obj U))).symm (𝟙 _))
          n x))) := by
  have h := ConcreteCategory.congr_hom (congrArg (fun α ↦ α.app U)
    (unit_comp_forget_map_pushforwardSymmetricPowerComparison_app φ n M)) x
  refine h.trans (congrArg (fun y ↦
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
      ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj M.val)) ≫
      (_root_.SheafOfModules.forget _).map (_root_.SheafOfModules.symmetricPowerIso n M).inv).app
        (F.op.obj U) y) ?_)
  -- Composites evaluate on sections by definition; it remains to compare the sectionwise
  -- comparison with the induced map of symmetric algebras.
  exact Subtype.ext <| (PresheafOfModules.coe_pushforwardSymmetricPowerComparison_app_app_apply
    (commRingCatHom φ) n M.val U x).trans
      (TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ n x).symm

/-- In degree one, the symmetric-power comparison of pushforward is the identity of `φ_* M`,
read through the identifications `Sym¹ M ≅ M`. -/
-- Not `@[simp]`: `symmetricPowerOneIso_hom_app` unfolds the left-hand side.
@[reassoc]
theorem pushforwardSymmetricPowerComparison_app_comp_map_symmetricPowerOneIso
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardSymmetricPowerComparison φ 1).app M ≫
        (_root_.SheafOfModules.pushforward φ).map
          ((_root_.SheafOfModules.symmetricPowerOneIso R).hom.app M) =
      (_root_.SheafOfModules.symmetricPowerOneIso S).hom.app
        ((_root_.SheafOfModules.pushforward φ).obj M) :=
  sheafifyPushforwardComparison_app_comp_pushforward_map φ _ _ _ _ _ M
    (oS := (PresheafOfModulesOfCommRing.symmetricPowerOneIso S.obj).hom.app
      ((_root_.SheafOfModules.pushforward φ).obj M).val)
    (oR := (PresheafOfModulesOfCommRing.symmetricPowerOneIso R.obj).hom.app M.val)
    (by rw [_root_.SheafOfModules.symmetricPowerOneIso_hom_app, Iso.inv_hom_id_assoc])
    (by rw [_root_.SheafOfModules.symmetricPowerOneIso_hom_app, Iso.inv_hom_id_assoc])
    (PresheafOfModules.pushforwardSymmetricPowerComparison_app_comp_map_symmetricPowerOneIso
      (commRingCatHom φ) M.val)

/-- Restriction along a continuous and cocontinuous functor with an isomorphism of coefficient
sheaves preserves every symmetric power. -/
instance isIso_pushforwardSymmetricPowerComparison [F.IsCocontinuous J K] [IsIso φ] (n : ℕ) :
    IsIso (pushforwardSymmetricPowerComparison φ n) := by
  have hα : IsIso (commRingCatHom φ) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      ((ConcreteCategory.isIso_iff_bijective (φ.hom.app U)).mp inferInstance)
  unfold pushforwardSymmetricPowerComparison
  infer_instance

variable {φ} {G : _root_.SheafOfModules.{u} (ringCatSheaf S) ⥤
    _root_.SheafOfModules.{u} (ringCatSheaf R)} (adj : G ⊣ _root_.SheafOfModules.pushforward φ)

/-- The canonical map `G (Symⁿ M) ⟶ Symⁿ (G M)` for a left adjoint `G` of pushforward: the
mate of `pushforwardSymmetricPowerComparison φ n` under `adj`. -/
def pullbackSymmetricPowerComparison (n : ℕ) :
    _root_.SheafOfModules.symmetricPower S n ⋙ G ⟶
      G ⋙ _root_.SheafOfModules.symmetricPower R n :=
  (mateEquiv adj adj).symm (pushforwardSymmetricPowerComparison φ n)

/-- The mate of the symmetric-power pullback comparison is the pushforward comparison. -/
-- Not a simp lemma: `mateEquiv_apply` expands its left-hand side first.
theorem mateEquiv_pullbackSymmetricPowerComparison (n : ℕ) :
    mateEquiv adj adj (pullbackSymmetricPowerComparison adj n) =
      pushforwardSymmetricPowerComparison φ n :=
  Equiv.apply_symm_apply _ _

/-- The adjunction equation characterizing the pullback comparison. -/
@[reassoc (attr := simp)]
theorem unit_comp_pushforward_pullbackSymmetricPowerComparison (n : ℕ)
    (M : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    adj.unit.app ((_root_.SheafOfModules.symmetricPower S n).obj M) ≫
      (_root_.SheafOfModules.pushforward φ).map
        ((pullbackSymmetricPowerComparison adj n).app M) =
    (_root_.SheafOfModules.symmetricPower S n).map (adj.unit.app M) ≫
      (pushforwardSymmetricPowerComparison φ n).app (G.obj M) :=
  (unit_mateEquiv_symm adj adj
    (TwoSquare.mk _ _ _ _ (pushforwardSymmetricPowerComparison φ n)) M).symm

/-- On the sheafification of a sectionwise symmetric tensor `x` in the image of the adjunction
unit, the pullback comparison takes the sheafification of the image of `x` under the map of
symmetric algebras induced by the unit. -/
@[simp]
theorem pullbackSymmetricPowerComparison_app_val_app_unit (n : ℕ)
    (M : _root_.SheafOfModules.{u} (ringCatSheaf S)) (U : Cᵒᵖ)
    (x : (PresheafOfModulesOfCommRing.obj (R := S.obj) M.val U).symmetricPower n) :
    dsimp% only [Functor.comp_obj, ObjectProperty.ι_obj, Functor.id_obj, Functor.op_obj]
    (((pullbackSymmetricPowerComparison adj n).app M).val.app (F.op.obj U)
      ((adj.unit.app ((_root_.SheafOfModules.symmetricPower S n).obj M)).val.app U
        ((_root_.SheafOfModules.symmetricPowerIso n M).inv.val.app U
          (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).unit.app
            ((PresheafOfModulesOfCommRing.symmetricPower (R := S.obj) n).obj M.val)).app U x))) =
    (_root_.SheafOfModules.symmetricPowerIso n (G.obj M)).inv.val.app (F.op.obj U)
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
          ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj (G.obj M).val)).app
            (F.op.obj U)
        (TauCeti.SymmetricAlgebra.homogeneousSubmoduleMapₛₗ
          ((_root_.ModuleCat.semilinearMapAddEquiv ((commRingCatHom φ).app U).hom
            (PresheafOfModulesOfCommRing.obj (R := S.obj) M.val U)
            (PresheafOfModulesOfCommRing.obj (R := R.obj) (G.obj M).val (F.op.obj U))).symm
              ((adj.unit.app M).val.app U)) n x))) := by
  have h := ConcreteCategory.congr_hom (congrArg (fun α ↦ α.val.app U)
    (unit_comp_pushforward_pullbackSymmetricPowerComparison adj n M))
    ((_root_.SheafOfModules.symmetricPowerIso n M).inv.val.app U
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower (R := S.obj) n).obj M.val)).app U x))
  -- As in `pushforwardSymmetricPowerComparison_app_val_app_unit`, composites evaluate on
  -- sections by definition; compute `Symⁿ` of the unit and then the pushforward comparison.
  refine h.trans ?_
  refine (congrArg (((pushforwardSymmetricPowerComparison φ n).app (G.obj M)).val.app U)
    (_root_.SheafOfModules.symmetricPower_map_val_app_unit n (adj.unit.app M) U x)).trans ?_
  refine (pushforwardSymmetricPowerComparison_app_val_app_unit φ n (G.obj M) U _).trans ?_
  refine congrArg (fun y ↦ (_root_.SheafOfModules.symmetricPowerIso n (G.obj M)).inv.val.app
    (F.op.obj U) (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
      ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj (G.obj M).val)).app
        (F.op.obj U) y)) (Subtype.ext ?_)
  refine (TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ n _).trans ?_
  refine (congrArg (SymmetricAlgebra.mapₛₗ _)
    (ModuleCat.symmetricPower.coe_map_apply _ n x)).trans ?_
  refine (congrArg (SymmetricAlgebra.mapₛₗ _)
    (RingHom.congr_fun (SymmetricAlgebra.mapₛₗ_eq_map _).symm x.1)).trans ?_
  -- The two induced ring homomorphisms compose to the one induced by the unit; the underlying
  -- functions of the semilinear maps agree by definition.
  rw [TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply, ← RingHom.comp_apply,
    SymmetricAlgebra.mapₛₗ_comp_mapₛₗ] <;> intro <;> rfl

/-- In degree one, the pullback comparison is the identity of `G M`, read through the
identifications `Sym¹ M ≅ M`. -/
-- Not `@[simp]`: `symmetricPowerOneIso_hom_app` unfolds the left-hand side.
@[reassoc]
theorem pullbackSymmetricPowerComparison_app_comp_symmetricPowerOneIso
    (M : _root_.SheafOfModules.{u} (ringCatSheaf S)) :
    (pullbackSymmetricPowerComparison adj 1).app M ≫
        (_root_.SheafOfModules.symmetricPowerOneIso R).hom.app (G.obj M) =
      G.map ((_root_.SheafOfModules.symmetricPowerOneIso S).hom.app M) := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    unit_comp_pushforward_pullbackSymmetricPowerComparison_assoc,
    pushforwardSymmetricPowerComparison_app_comp_map_symmetricPowerOneIso]
  exact ((_root_.SheafOfModules.symmetricPowerOneIso S).hom.naturality _).trans
    (adj.unit.naturality _)

/-- The pullback comparison is an isomorphism in degree one. -/
instance isIso_pullbackSymmetricPowerComparison_one :
    IsIso (pullbackSymmetricPowerComparison adj 1) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [(Iso.eq_comp_inv ((_root_.SheafOfModules.symmetricPowerOneIso R).app _)).mpr
    (pullbackSymmetricPowerComparison_app_comp_symmetricPowerOneIso adj M)]
  infer_instance

end

end TauCeti.SheafOfModules
