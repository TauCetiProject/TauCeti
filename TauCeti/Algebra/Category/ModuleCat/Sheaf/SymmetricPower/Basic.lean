/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.SymmetricPower
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Basic

/-!
# Symmetric powers of sheaves of modules

Given a site `(C, J)` carrying a sheaf of commutative rings `R` and `n : ℕ`, the `n`-th symmetric
power of a sheaf of `R`-modules `M` is obtained by taking sectionwise symmetric powers
`Sym^n_{R(U)} M(U)` (`PresheafOfModulesOfCommRing.symmetricPower`, the degree-`n` parts of the
sectionwise symmetric algebras) and sheafifying, exactly as the tensor product
`TauCeti.SheafOfModules.tensorProduct` sheafifies sectionwise tensor products and
`SheafOfModules.exteriorPower` sheafifies sectionwise exterior powers. On a scheme `X` this gives
`SheafOfModules.symmetricPower X.sheaf n : X.Modules ⥤ X.Modules`, the symmetric powers of
`𝒪ₓ`-modules. They are the graded pieces of the symmetric algebra `Sym(F) = ⨁ₙ Symⁿ(F)` of an
`𝒪ₓ`-module `F`, whose relative spectrum is the linear scheme of a quasi-coherent `F`.

## Main declarations

* `SheafOfModules.symmetricPower R n` is the `n`-th symmetric power, as an endofunctor of
  sheaves of `R`-modules;
* `SheafOfModules.symmetricPowerIso` and `SheafOfModules.symmetricPower_map` are its
  defining identification with the sheafification of the sectionwise symmetric power;
* `SheafOfModules.symmetricPowerZeroIso` identifies `Sym⁰ M` with the structure sheaf;
* `SheafOfModules.symmetricPowerOneIso` identifies `Sym¹ M` with `M`;
* `SheafOfModules.overSymmetricPowerIso` identifies the restriction of `Symⁿ M` to a slice site
  with the symmetric power of the restriction of `M`.
-/

public section

open CategoryTheory
open TauCeti.SheafOfModules (ringCatSheaf)

universe u v₁ v₂ u₁ u₂

noncomputable section

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})

namespace SheafOfModules

/-- The `n`-th symmetric power of sheaves of `R`-modules: the sectionwise symmetric power of the
underlying presheaf of modules, sheafified. -/
def symmetricPower (n : ℕ) :
    SheafOfModules.{u} (ringCatSheaf R) ⥤ SheafOfModules.{u} (ringCatSheaf R) :=
  (SheafOfModules.forget (ringCatSheaf R)).comp
    ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).comp
      (PresheafOfModules.sheafification (R₀ := (ringCatSheaf R).obj) (𝟙 _)))

variable {R}

/-- The defining identification of the symmetric power of a sheaf of modules with the
sheafification of the sectionwise symmetric power of its underlying presheaf of modules. -/
def symmetricPowerIso (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (symmetricPower R n).obj M ≅
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
        ((PresheafOfModulesOfCommRing.symmetricPower n).obj M.val) :=
  Iso.refl _

/-- The symmetric power of a morphism of sheaves of modules is the sheafification of the
sectionwise symmetric power of the underlying morphism of presheaves of modules. -/
theorem symmetricPower_map (n : ℕ) {M N : SheafOfModules.{u} (ringCatSheaf R)} (φ : M ⟶ N) :
    (symmetricPower R n).map φ =
      (symmetricPowerIso n M).hom ≫ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
        ((PresheafOfModulesOfCommRing.symmetricPower n).map φ.val) ≫ (symmetricPowerIso n N).inv :=
  (rfl)

variable (R) in
/-- The zeroth symmetric power of a sheaf of modules is the structure sheaf, naturally: the
sheafification of the presheaf-level identification
`PresheafOfModulesOfCommRing.symmetricPowerZeroIso`, followed by the identification of the
sheafified unit with the structure sheaf. -/
def symmetricPowerZeroIso :
    symmetricPower R 0 ≅ (Functor.const _).obj (SheafOfModules.unit (ringCatSheaf R)) :=
  Functor.isoWhiskerLeft (SheafOfModules.forget (ringCatSheaf R))
      (Functor.isoWhiskerRight (PresheafOfModulesOfCommRing.symmetricPowerZeroIso R.obj)
        (PresheafOfModules.sheafification (R₀ := (ringCatSheaf R).obj) (𝟙 _))) ≪≫
    NatIso.ofComponents
      (fun _ ↦ TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R)
        (SheafOfModules.unit (ringCatSheaf R)))
      -- the sheafified constant functor sends every morphism to the identity
      (fun _ ↦ (congrArg (· ≫ _) ((PresheafOfModules.sheafification
        (R₀ := (ringCatSheaf R).obj) (𝟙 _)).map_id (PresheafOfModulesOfCommRing.unit R.obj))).trans
          ((Category.id_comp _).trans (Category.comp_id _).symm))

variable (R) in
/-- The first symmetric power of a sheaf of modules is the sheaf itself, naturally: the
sheafification of the presheaf-level identification
`PresheafOfModulesOfCommRing.symmetricPowerOneIso`, followed by the counit
`TauCeti.SheafOfModules.sheafificationIso`. -/
def symmetricPowerOneIso : symmetricPower R 1 ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft (SheafOfModules.forget (ringCatSheaf R))
      (Functor.isoWhiskerRight (PresheafOfModulesOfCommRing.symmetricPowerOneIso R.obj)
        (PresheafOfModules.sheafification (R₀ := (ringCatSheaf R).obj) (𝟙 _))) ≪≫
    NatIso.ofComponents (TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R))
      TauCeti.SheafOfModules.sheafificationIso_hom_naturality

/-- On components, `symmetricPowerZeroIso` is the sheafification of the presheaf-level
identification `PresheafOfModulesOfCommRing.symmetricPowerZeroIso`, followed by the
identification of the sheafified unit with the structure sheaf. -/
@[simp, reassoc]
theorem symmetricPowerZeroIso_hom_app (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (symmetricPowerZeroIso R).hom.app M =
      (symmetricPowerIso 0 M).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          ((PresheafOfModulesOfCommRing.symmetricPowerZeroIso R.obj).hom.app M.val) ≫
        (TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R)
          (SheafOfModules.unit (ringCatSheaf R))).hom :=
  (rfl)

/-- On components, `symmetricPowerOneIso` is the sheafification of the presheaf-level
identification `PresheafOfModulesOfCommRing.symmetricPowerOneIso`, followed by the counit
`TauCeti.SheafOfModules.sheafificationIso`. -/
@[simp, reassoc]
theorem symmetricPowerOneIso_hom_app (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (symmetricPowerOneIso R).hom.app M =
      (symmetricPowerIso 1 M).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          ((PresheafOfModulesOfCommRing.symmetricPowerOneIso R.obj).hom.app M.val) ≫
        (TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R) M).hom :=
  (rfl)

section Pushforward

open TauCeti.SheafOfModules (pushforwardCommRing pushforwardModule pushforwardRingIso
  pushforwardSheafificationIso pushforwardSheafificationNatIso
  pushforwardSheafificationNatIso_hom_app)

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F : D ⥤ C) [F.IsContinuous K J] [F.IsCocontinuous K J]

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.IsCocontinuous K J] [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Symmetric powers of presheaves of modules commute with pushforward of the underlying
presheaves. -/
def presheafPushforwardSymmetricPowerIso (n : ℕ) :
    PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n ⋙
        (PresheafOfModules.pushforward (F := F)
            (pushforwardRingIso (J := K) F (ringCatSheaf R)).inv :
          PresheafOfModules.{u} (ringCatSheaf R).obj ⥤
            PresheafOfModules.{u} (ringCatSheaf (pushforwardCommRing (J := K) F R)).obj) ≅
      (PresheafOfModules.pushforward (F := F)
          (pushforwardRingIso (J := K) F (ringCatSheaf R)).inv :
        PresheafOfModules.{u} (ringCatSheaf R).obj ⥤
          PresheafOfModules.{u} (ringCatSheaf (pushforwardCommRing (J := K) F R)).obj) ⋙
        PresheafOfModulesOfCommRing.symmetricPower
          (R := (pushforwardCommRing (J := K) F R).obj) n :=
  NatIso.ofComponents
    (fun M ↦ PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun _ _ f ↦ by
      ext x
      apply Subtype.ext
      exact (PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply
        n M (F.op.map f) x).trans
          (PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply n
            ((PresheafOfModules.pushforward (F := F)
              (pushforwardRingIso (J := K) F (ringCatSheaf R)).inv :
                PresheafOfModules.{u} (ringCatSheaf R).obj ⥤
                  PresheafOfModules.{u}
                    (ringCatSheaf (pushforwardCommRing (J := K) F R)).obj).obj M)
            f x).symm))
    (fun _ ↦ by
      ext X : 1
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.IsCocontinuous K J] [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- On sections, `presheafPushforwardSymmetricPowerIso` is the identity. -/
@[simp]
theorem presheafPushforwardSymmetricPowerIso_hom_app_app (n : ℕ)
    (M : PresheafOfModules.{u} (ringCatSheaf R).obj) (X : Dᵒᵖ) :
    ((presheafPushforwardSymmetricPowerIso (K := K) F n).hom.app M).app X = 𝟙 _ := by
  ext x
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.IsCocontinuous K J] [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- On sections, the inverse of `presheafPushforwardSymmetricPowerIso` is the identity. -/
@[simp]
theorem presheafPushforwardSymmetricPowerIso_inv_app_app (n : ℕ)
    (M : PresheafOfModules.{u} (ringCatSheaf R).obj) (X : Dᵒᵖ) :
    ((presheafPushforwardSymmetricPowerIso (K := K) F n).inv.app M).app X = 𝟙 _ := by
  ext x
  rfl

/-- Pushforward along a continuous and cocontinuous functor commutes with symmetric powers of
sheaves of modules. -/
def pushforwardSymmetricPowerIso (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardModule (J := K) F R).obj ((symmetricPower R n).obj M) ≅
      (symmetricPower (pushforwardCommRing (J := K) F R) n).obj
        ((pushforwardModule (J := K) F R).obj M) :=
  (pushforwardModule (J := K) F R).mapIso (symmetricPowerIso n M) ≪≫
    pushforwardSheafificationIso F (ringCatSheaf R)
      ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj M.val) ≪≫
    (PresheafOfModules.sheafification
      (𝟙 (ringCatSheaf (pushforwardCommRing (J := K) F R)).obj)).mapIso
        ((presheafPushforwardSymmetricPowerIso (K := K) F n).app M.val) ≪≫
    (symmetricPowerIso n ((pushforwardModule (J := K) F R).obj M)).symm

/-- The forward map of `pushforwardSymmetricPowerIso` is the sheafification--pushforward
comparison followed by the sheafified sectionwise comparison. -/
@[simp]
theorem pushforwardSymmetricPowerIso_hom (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardSymmetricPowerIso F n M).hom =
      (pushforwardModule (J := K) F R).map (symmetricPowerIso n M).hom ≫
        (pushforwardSheafificationIso F (ringCatSheaf R)
          ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj M.val)).hom ≫
        (PresheafOfModules.sheafification
          (𝟙 (ringCatSheaf (pushforwardCommRing (J := K) F R)).obj)).map
            ((presheafPushforwardSymmetricPowerIso (K := K) F n).hom.app M.val) ≫
        (symmetricPowerIso n ((pushforwardModule (J := K) F R).obj M)).inv :=
  (rfl)

/-- The natural isomorphism whose components are `pushforwardSymmetricPowerIso`. -/
private def pushforwardSymmetricPowerNatIso (n : ℕ) :
    symmetricPower R n ⋙ pushforwardModule (J := K) F R ≅
      pushforwardModule (J := K) F R ⋙ symmetricPower (pushforwardCommRing (J := K) F R) n :=
  Functor.isoWhiskerLeft (SheafOfModules.forget (ringCatSheaf R) ⋙
      PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n)
      (pushforwardSheafificationNatIso F (ringCatSheaf R)) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (SheafOfModules.forget (ringCatSheaf R))
      (presheafPushforwardSymmetricPowerIso (K := K) F n))
      (PresheafOfModules.sheafification
        (R₀ := (ringCatSheaf (pushforwardCommRing (J := K) F R)).obj)
        (R := ringCatSheaf (pushforwardCommRing (J := K) F R)) (𝟙 _))

private theorem pushforwardSymmetricPowerIso_hom_eq (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardSymmetricPowerIso F n M).hom =
      (pushforwardSymmetricPowerNatIso (K := K) F n).hom.app M :=
  -- the remaining factors agree definitionally (`symmetricPowerIso` is `Iso.refl`), so only the
  -- component of the sheafification--pushforward comparison needs its component lemma
  (congrArg (· ≫ (PresheafOfModules.sheafification
      (𝟙 (ringCatSheaf (pushforwardCommRing (J := K) F R)).obj)).map
        ((presheafPushforwardSymmetricPowerIso (K := K) F n).hom.app M.val))
    (pushforwardSheafificationNatIso_hom_app F (ringCatSheaf R)
      ((PresheafOfModulesOfCommRing.symmetricPower (R := R.obj) n).obj M.val))).symm

/-- `pushforwardSymmetricPowerIso` is natural in the sheaf of modules. -/
@[reassoc]
theorem pushforwardSymmetricPowerIso_hom_naturality (n : ℕ)
    {M N : SheafOfModules.{u} (ringCatSheaf R)} (φ : M ⟶ N) :
    (pushforwardModule (J := K) F R).map ((symmetricPower R n).map φ) ≫
        (pushforwardSymmetricPowerIso F n N).hom =
      (pushforwardSymmetricPowerIso F n M).hom ≫
        (symmetricPower (pushforwardCommRing (J := K) F R) n).map
          ((pushforwardModule (J := K) F R).map φ) := by
  rw [pushforwardSymmetricPowerIso_hom_eq, pushforwardSymmetricPowerIso_hom_eq]
  exact (pushforwardSymmetricPowerNatIso (K := K) F n).hom.naturality φ

/-- The restriction of a symmetric power to a slice site is the symmetric power of the
restriction. -/
def overSymmetricPowerIso (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) (X : C)
    [(J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ((symmetricPower R n).obj M).over X ≅ (symmetricPower (R.over X) n).obj (M.over X) :=
  pushforwardSymmetricPowerIso (K := J.over X) (Over.forget X) n M

/-- The forward map of `overSymmetricPowerIso` is the slice-site pushforward comparison. -/
@[simp]
theorem overSymmetricPowerIso_hom (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) (X : C)
    [(J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (overSymmetricPowerIso n M X).hom =
      (pushforwardSymmetricPowerIso (K := J.over X) (Over.forget X) n M).hom :=
  (rfl)

/-- `overSymmetricPowerIso` is natural in the sheaf of modules. -/
@[reassoc]
theorem overSymmetricPowerIso_hom_naturality (n : ℕ)
    {M N : SheafOfModules.{u} (ringCatSheaf R)} (φ : M ⟶ N) (X : C)
    [(J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ((symmetricPower R n).map φ).over X ≫ (overSymmetricPowerIso n N X).hom =
      (overSymmetricPowerIso n M X).hom ≫ (symmetricPower (R.over X) n).map (φ.over X) :=
  pushforwardSymmetricPowerIso_hom_naturality (K := J.over X) (Over.forget X) n φ

end Pushforward

end SheafOfModules

end
