/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.SymmetricPower.Pullback
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pushforward

/-!
# The symmetric-power pullback comparison for sheaves of modules

Let `F : C ⥤ D` be a continuous functor between sites, `S` and `R` sheaves of commutative
rings, and `φ : S ⟶ F_* R`. This file constructs the canonical natural map
`Symⁿ (φ_* M) ⟶ φ_* (Symⁿ M)`. It is the sheafification of the sectionwise comparison followed
by the unit of sheafification of `Symⁿ M`.

Its mate under an adjunction `G ⊣ φ_*` is the canonical natural map
`G (Symⁿ M) ⟶ Symⁿ (G M)`. The adjunction is an explicit argument, so the same construction
applies both to pullback of sheaves of modules and to pullback of modules on schemes. In degree
one the comparison is an isomorphism for every such adjunction.

The construction follows
`TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Pullback`, with the exterior-power
comparison replaced by the symmetric-power comparison of underlying presheaves.

## Main declarations

* `TauCeti.SheafOfModules.pushforwardSymmetricPowerComparison`: the canonical map
  `Symⁿ (φ_* M) ⟶ φ_* (Symⁿ M)`;
* `TauCeti.SheafOfModules.pullbackSymmetricPowerComparison`: its mate
  `G (Symⁿ M) ⟶ Symⁿ (G M)`.

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

/-- The presheaf map transposed to the pushforward comparison: the sectionwise comparison
followed by the pushforward of the sheafification unit of `Symⁿ M`. -/
private def pushforwardSymmetricPowerPresheafMap (n : ℕ)
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (PresheafOfModulesOfCommRing.symmetricPower (R := S.obj) n).obj
        ((_root_.SheafOfModules.pushforward φ).obj M).val ⟶
      (_root_.SheafOfModules.forget _).obj ((_root_.SheafOfModules.pushforward φ).obj
        ((_root_.SheafOfModules.symmetricPower R n).obj M)) :=
  (PresheafOfModules.pushforwardSymmetricPowerComparison (commRingCatHom φ) n).app M.val ≫
    (presheafPushforward φ).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj M.val) ≫
        (_root_.SheafOfModules.forget _).map (_root_.SheafOfModules.symmetricPowerIso n M).inv)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private lemma pushforwardSymmetricPowerPresheafMap_naturality (n : ℕ)
    {M N : _root_.SheafOfModules.{u} (ringCatSheaf R)} (f : M ⟶ N) :
    (PresheafOfModulesOfCommRing.symmetricPower (R := S.obj) n).map
        ((_root_.SheafOfModules.pushforward φ).map f).val ≫
      pushforwardSymmetricPowerPresheafMap φ n N =
    pushforwardSymmetricPowerPresheafMap φ n M ≫
      (_root_.SheafOfModules.forget _).map ((_root_.SheafOfModules.pushforward φ).map
        ((_root_.SheafOfModules.symmetricPower R n).map f)) := by
  have h := (PresheafOfModules.pushforwardSymmetricPowerComparison
    (commRingCatHom φ) n).naturality f.val
  have hu := (PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringCatSheaf R).obj)).unit.naturality
      ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).map f.val)
  have hk : (PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).map f.val ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj N.val) ≫
        (_root_.SheafOfModules.forget _).map (_root_.SheafOfModules.symmetricPowerIso n N).inv =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj M.val) ≫
        (_root_.SheafOfModules.forget _).map (_root_.SheafOfModules.symmetricPowerIso n M).inv) ≫
        (_root_.SheafOfModules.forget _).map
          ((_root_.SheafOfModules.symmetricPower R n).map f) := by
    have e : (_root_.SheafOfModules.forget _).map
          (_root_.SheafOfModules.symmetricPowerIso n M).inv ≫
        (_root_.SheafOfModules.forget _).map
          ((_root_.SheafOfModules.symmetricPower R n).map f) =
        (_root_.SheafOfModules.forget _).map ((PresheafOfModules.sheafification (𝟙 _)).map
          ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).map f.val)) ≫
        (_root_.SheafOfModules.forget _).map
          (_root_.SheafOfModules.symmetricPowerIso n N).inv := by
      rw [← Functor.map_comp, ← Functor.map_comp, _root_.SheafOfModules.symmetricPower_map,
        Iso.inv_hom_id_assoc]
    -- These presheaf categories agree after unfolding the composed ring sheaves, so reassociate
    -- explicitly rather than asking rewriting to cross the wrapper.
    exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hu)).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e.symm).trans
        (Category.assoc _ _ _).symm))
  rw [pushforwardSymmetricPowerPresheafMap, pushforwardSymmetricPowerPresheafMap,
    forget_map_pushforward_map]
  refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h)).trans ?_
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((presheafPushforward φ).map_comp _ _).symm).trans ?_)
  refine (congrArg (fun g ↦ _ ≫ (presheafPushforward φ).map g) hk).trans ?_
  exact (congrArg (_ ≫ ·) ((presheafPushforward φ).map_comp _ _)).trans
    (Category.assoc _ _ _).symm

/-- The canonical natural map `Symⁿ (φ_* M) ⟶ φ_* (Symⁿ M)`. It is the transpose along
sheafification of the sectionwise symmetric-power comparison followed by sheafification. -/
def pushforwardSymmetricPowerComparison (n : ℕ) :
    _root_.SheafOfModules.pushforward φ ⋙ _root_.SheafOfModules.symmetricPower S n ⟶
      _root_.SheafOfModules.symmetricPower R n ⋙ _root_.SheafOfModules.pushforward φ where
  app M := (_root_.SheafOfModules.symmetricPowerIso n _).hom ≫
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)).homEquiv _ _).symm
      (pushforwardSymmetricPowerPresheafMap φ n M)
  naturality M N f := by
    rw [Functor.comp_map, Functor.comp_map, _root_.SheafOfModules.symmetricPower_map,
      Category.assoc, Category.assoc, Iso.inv_hom_id_assoc]
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)
    exact (congrArg (_ ≫ ·) ((adj.homEquiv_naturality_left_symm _ _).symm.trans
        ((congrArg _ (pushforwardSymmetricPowerPresheafMap_naturality φ n f)).trans
          (adj.homEquiv_naturality_right_symm _ _)))).trans
      (Category.assoc _ _ _).symm

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
            (_root_.SheafOfModules.symmetricPowerIso n M).inv) := by
  rw [pushforwardSymmetricPowerComparison, Iso.inv_hom_id_assoc]
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringCatSheaf S).obj)).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)

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
        ((_root_.SheafOfModules.pushforward φ).obj M) := by
  rw [← cancel_epi (_root_.SheafOfModules.symmetricPowerIso 1
    ((_root_.SheafOfModules.pushforward φ).obj M)).inv]
  apply ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (ringCatSheaf S).obj)).homEquiv _ _).injective
  have key : (PresheafOfModules.sheafificationAdjunction
        (𝟙 (ringCatSheaf S).obj)).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower (R := S.obj) 1).obj
          ((_root_.SheafOfModules.pushforward φ).obj M).val) ≫
      ((_root_.SheafOfModules.symmetricPowerIso 1 _).inv ≫
          (pushforwardSymmetricPowerComparison φ 1).app M).val ≫
        ((_root_.SheafOfModules.pushforward φ).map
          ((_root_.SheafOfModules.symmetricPowerOneIso R).hom.app M)).val =
      (PresheafOfModulesOfCommRing.symmetricPowerOneIso S.obj).hom.app
        ((_root_.SheafOfModules.pushforward φ).obj M).val := by
    let P := presheafPushforward φ
    let c : (PresheafOfModulesOfCommRing.symmetricPower (R := S.obj) 1).obj
        ((_root_.SheafOfModules.pushforward φ).obj M).val ⟶
          P.obj ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) 1).obj M.val) :=
      (PresheafOfModules.pushforwardSymmetricPowerComparison
        (commRingCatHom φ) 1).app M.val
    let η := (PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringCatSheaf R).obj)).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) 1).obj M.val)
    let f : (_root_.SheafOfModules.symmetricPower R 1).obj M ⟶ M :=
      (_root_.SheafOfModules.symmetricPowerOneIso R).hom.app M
    let o : (PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) 1).obj M.val ⟶ M.val :=
      (PresheafOfModulesOfCommRing.symmetricPowerOneIso R.obj).hom.app M.val
    let o' : (PresheafOfModulesOfCommRing.symmetricPower (R := S.obj) 1).obj
        ((_root_.SheafOfModules.pushforward φ).obj M).val ⟶ P.obj M.val :=
      (PresheafOfModulesOfCommRing.symmetricPowerOneIso S.obj).hom.app
        ((_root_.SheafOfModules.pushforward φ).obj M).val
    calc
      _ = c ≫ P.map (η ≫ (_root_.SheafOfModules.symmetricPowerIso 1 M).inv.val) ≫ P.map f.val :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ P.map f.val)
          (unit_comp_forget_map_pushforwardSymmetricPowerComparison_app φ 1 M)).trans
            (Category.assoc _ _ _))
      _ = c ≫ P.map (η ≫ ((_root_.SheafOfModules.symmetricPowerIso 1 M).inv ≫ f).val) :=
        congrArg (c ≫ ·) ((P.map_comp _ _).symm.trans
          (congrArg P.map (Category.assoc _ _ _)))
      _ = c ≫ P.map o :=
        congrArg (fun g ↦ c ≫ P.map g)
          (_root_.SheafOfModules.unit_comp_val_symmetricPowerOneIso_hom_app M)
      _ = o' :=
        PresheafOfModules.pushforwardSymmetricPowerComparison_app_comp_map_symmetricPowerOneIso
          (commRingCatHom φ) M.val
  refine (Adjunction.homEquiv_unit _ _ _ _).trans ?_
  refine key.trans ?_
  refine (_root_.SheafOfModules.unit_comp_val_symmetricPowerOneIso_hom_app
    ((_root_.SheafOfModules.pushforward φ).obj M)).symm.trans ?_
  exact (Adjunction.homEquiv_unit
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf S).obj)) _ _
    ((_root_.SheafOfModules.symmetricPowerIso 1 _).inv ≫
      (_root_.SheafOfModules.symmetricPowerOneIso S).hom.app
        ((_root_.SheafOfModules.pushforward φ).obj M))).symm

variable {φ} {G : _root_.SheafOfModules.{u} (ringCatSheaf S) ⥤
    _root_.SheafOfModules.{u} (ringCatSheaf R)} (adj : G ⊣ _root_.SheafOfModules.pushforward φ)

/-- The canonical map `G (Symⁿ M) ⟶ Symⁿ (G M)` for a left adjoint `G` of pushforward: the
mate of `pushforwardSymmetricPowerComparison φ n` under `adj`. -/
def pullbackSymmetricPowerComparison (n : ℕ) :
    _root_.SheafOfModules.symmetricPower S n ⋙ G ⟶
      G ⋙ _root_.SheafOfModules.symmetricPower R n :=
  (mateEquiv adj adj).symm (pushforwardSymmetricPowerComparison φ n)

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
