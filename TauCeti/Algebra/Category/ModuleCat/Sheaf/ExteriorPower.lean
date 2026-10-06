/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Basic

/-!
# Exterior powers of sheaves of modules

Given a site `(C, J)` carrying a sheaf of commutative rings `R` and `n : ℕ`, the `n`-th exterior
power of a sheaf of `R`-modules `M` is obtained by taking sectionwise exterior powers
`⋀[R(U)]^n M(U)` (`PresheafOfModulesOfCommRing.exteriorPower`) and sheafifying, exactly as
the tensor product `TauCeti.SheafOfModules.tensorProduct` sheafifies sectionwise tensor products.
On a scheme `X` this gives `SheafOfModules.exteriorPower X.sheaf n : X.Modules ⥤ X.Modules`, the
exterior powers of `𝒪ₓ`-modules from which determinants of vector bundles are built.

## Main declarations

* `SheafOfModules.exteriorPower R n` is the `n`-th exterior power, as an endofunctor of
  sheaves of `R`-modules;
* `SheafOfModules.exteriorPowerIso` and `SheafOfModules.exteriorPower_map` are its
  defining identification with the sheafification of the sectionwise exterior power;
* `SheafOfModules.exteriorPowerZeroIso` identifies `⋀⁰ M` with the structure sheaf;
* `SheafOfModules.exteriorPowerOneIso` identifies `⋀¹ M` with `M`;
* `SheafOfModules.presheafPushforwardExteriorPowerIso` identifies the exterior power of the
  pushforward of a presheaf of modules with the pushforward of its exterior power;
* `SheafOfModules.pushforwardExteriorPowerIso` identifies the pushforward of `⋀ⁿ M` along a
  continuous and cocontinuous functor with the exterior power of the pushforward of `M`, and
  `SheafOfModules.overExteriorPowerIso` specializes it to the restriction `(⋀ⁿ M)|_X ≅ ⋀ⁿ (M|_X)`
  to a slice site; both are natural in `M` (`pushforwardExteriorPowerIso_hom_naturality`,
  `overExteriorPowerIso_hom_naturality`).

The restriction comparison lets local computations of exterior powers, such as those on the
charts of a locally free sheaf, be carried out on the restriction to a covering object.
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

/-- The `n`-th exterior power of sheaves of `R`-modules: the sectionwise exterior power of the
underlying presheaf of modules, sheafified. -/
def exteriorPower (n : ℕ) :
    SheafOfModules.{u} (ringCatSheaf R) ⥤ SheafOfModules.{u} (ringCatSheaf R) :=
  (SheafOfModules.forget (ringCatSheaf R)).comp
    ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).comp
      (PresheafOfModules.sheafification (R₀ := (ringCatSheaf R).obj) (𝟙 _)))

variable {R}

/-- The defining identification of the exterior power of a sheaf of modules with the
sheafification of the sectionwise exterior power of its underlying presheaf of modules. -/
def exteriorPowerIso (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (exteriorPower R n).obj M ≅
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
        ((PresheafOfModulesOfCommRing.exteriorPower n).obj M.val) :=
  Iso.refl _

/-- The exterior power of a morphism of sheaves of modules is the sheafification of the
sectionwise exterior power of the underlying morphism of presheaves of modules. -/
theorem exteriorPower_map (n : ℕ) {M N : SheafOfModules.{u} (ringCatSheaf R)} (φ : M ⟶ N) :
    (exteriorPower R n).map φ =
      (exteriorPowerIso n M).hom ≫ (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
        ((PresheafOfModulesOfCommRing.exteriorPower n).map φ.val) ≫ (exteriorPowerIso n N).inv :=
  (rfl)

variable (R) in
/-- The zeroth exterior power of a sheaf of modules is the structure sheaf, naturally. -/
def exteriorPowerZeroIso :
    exteriorPower R 0 ≅ (Functor.const _).obj (SheafOfModules.unit (ringCatSheaf R)) :=
  NatIso.ofComponents
    (fun M ↦ exteriorPowerIso 0 M ≪≫
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso
        ((PresheafOfModulesOfCommRing.exteriorPowerZeroIso R.obj).app M.val) ≪≫
      TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R)
        (SheafOfModules.unit (ringCatSheaf R)))
    (fun {M N} φ ↦ by
      rw [exteriorPower_map]
      simp only [Iso.trans_hom, Functor.const_obj_map, Category.assoc, Iso.inv_hom_id_assoc,
        Iso.cancel_iso_hom_left]
      -- `erw`: the presheaf-level isomorphism lives over `PresheafOfModulesOfCommRing R.obj`, which
      -- is presheaves of modules over `(ringCatSheaf R).obj` only after unfolding `sheafCompose`
      erw [Iso.trans_hom, Iso.trans_hom, ← Functor.map_comp_assoc, Iso.app_hom,
        NatTrans.naturality, Functor.const_obj_map, Category.comp_id]
      rfl)

variable (R) in
/-- The first exterior power of a sheaf of modules is the sheaf itself, naturally. -/
def exteriorPowerOneIso : exteriorPower R 1 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ exteriorPowerIso 1 M ≪≫
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso
        ((PresheafOfModulesOfCommRing.exteriorPowerOneIso R.obj).app M.val) ≪≫
      TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R) M)
    (fun {M N} φ ↦ by
      rw [exteriorPower_map]
      simp only [Iso.trans_hom, Functor.id_map, Category.assoc, Iso.inv_hom_id_assoc,
        Iso.cancel_iso_hom_left]
      -- `erw`: as in `exteriorPowerZeroIso`, the presheaf-level isomorphism lives over
      -- `PresheafOfModulesOfCommRing R.obj`, which agrees with the ambient category only up to
      -- unfolding `sheafCompose`
      erw [Functor.mapIso_hom, ← Functor.map_comp_assoc, Iso.app_hom, NatTrans.naturality]
      exact ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map_comp_assoc _ _ _).trans
        (congrArg _ (TauCeti.SheafOfModules.sheafificationIso_hom_naturality φ)))

/-- On components, `exteriorPowerZeroIso` is the sheafification of the presheaf-level
identification `PresheafOfModulesOfCommRing.exteriorPowerZeroIso`, followed by the identification of
the sheafified unit with the structure sheaf. -/
@[simp, reassoc]
theorem exteriorPowerZeroIso_hom_app (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (exteriorPowerZeroIso R).hom.app M =
      (exteriorPowerIso 0 M).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          ((PresheafOfModulesOfCommRing.exteriorPowerZeroIso R.obj).hom.app M.val) ≫
        (TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R)
          (SheafOfModules.unit (ringCatSheaf R))).hom :=
  (rfl)

/-- On components, `exteriorPowerOneIso` is the sheafification of the presheaf-level
identification `PresheafOfModulesOfCommRing.exteriorPowerOneIso`, followed by the counit
`TauCeti.SheafOfModules.sheafificationIso`. -/
@[simp, reassoc]
theorem exteriorPowerOneIso_hom_app (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (exteriorPowerOneIso R).hom.app M =
      (exteriorPowerIso 1 M).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          ((PresheafOfModulesOfCommRing.exteriorPowerOneIso R.obj).hom.app M.val) ≫
        (TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R) M).hom :=
  (rfl)

section Pushforward

open TauCeti.SheafOfModules (pushforwardCommRing pushforwardModule pushforwardRingIso
  pushforwardSheafificationIso pushforwardSheafificationIso_inv_naturality)

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F : D ⥤ C) [F.IsContinuous K J] [F.IsCocontinuous K J]

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.IsCocontinuous K J] [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Exterior powers of presheaves of modules commute with the pushforward of presheaves of modules
underlying `pushforwardModule F R`: over `X`, both sides have sections `⋀[R(F X)]^n M(F X)` and
the same restriction maps. -/
def presheafPushforwardExteriorPowerIso (n : ℕ) :
    PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n ⋙
        (PresheafOfModules.pushforward (F := F)
            (pushforwardRingIso (J := K) F (ringCatSheaf R)).inv :
          PresheafOfModules.{u} (ringCatSheaf R).obj ⥤
            PresheafOfModules.{u} (ringCatSheaf (pushforwardCommRing (J := K) F R)).obj) ≅
      (PresheafOfModules.pushforward (F := F)
          (pushforwardRingIso (J := K) F (ringCatSheaf R)).inv :
        PresheafOfModules.{u} (ringCatSheaf R).obj ⥤
          PresheafOfModules.{u} (ringCatSheaf (pushforwardCommRing (J := K) F R)).obj) ⋙
        PresheafOfModulesOfCommRing.exteriorPower (R := (pushforwardCommRing (J := K) F R).obj) n :=
  NatIso.ofComponents
    (fun M ↦ PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (fun X Y f ↦ by
      refine ModuleCat.exteriorPower.hom_ext (R := R.obj.obj (Opposite.op (F.obj X.unop))) ?_
      ext x
      exact (PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk n M (F.op.map f) x).trans
        (PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk n
          ((PresheafOfModules.pushforward (F := F)
            (pushforwardRingIso (J := K) F (ringCatSheaf R)).inv :
              PresheafOfModules.{u} (ringCatSheaf R).obj ⥤
                PresheafOfModules.{u} (ringCatSheaf (pushforwardCommRing (J := K) F R)).obj).obj M)
          f x).symm))
    (fun _ ↦ by
      ext X : 1
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.IsCocontinuous K J] [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- On sections, `presheafPushforwardExteriorPowerIso` is the identity of `⋀[R(F X)]^n M(F X)`. -/
@[simp]
theorem presheafPushforwardExteriorPowerIso_hom_app_app (n : ℕ)
    (M : PresheafOfModules.{u} (ringCatSheaf R).obj) (X : Dᵒᵖ) :
    ((presheafPushforwardExteriorPowerIso (K := K) F n).hom.app M).app X = 𝟙 _ :=
  (rfl)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.IsCocontinuous K J] [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- On sections, the inverse of `presheafPushforwardExteriorPowerIso` is the identity of
`⋀[R(F X)]^n M(F X)`. -/
@[simp]
theorem presheafPushforwardExteriorPowerIso_inv_app_app (n : ℕ)
    (M : PresheafOfModules.{u} (ringCatSheaf R).obj) (X : Dᵒᵖ) :
    ((presheafPushforwardExteriorPowerIso (K := K) F n).inv.app M).app X = 𝟙 _ :=
  (rfl)

/-- For each sheaf of modules `M`, pushforward along a continuous and cocontinuous functor
commutes with the `n`-th exterior power: `F_*(⋀ⁿ M) ≅ ⋀ⁿ (F_* M)`. -/
def pushforwardExteriorPowerIso (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardModule (J := K) F R).obj ((exteriorPower R n).obj M) ≅
      (exteriorPower (pushforwardCommRing (J := K) F R) n).obj
        ((pushforwardModule (J := K) F R).obj M) :=
  (pushforwardModule (J := K) F R).mapIso (exteriorPowerIso n M) ≪≫
    pushforwardSheafificationIso F (ringCatSheaf R)
      ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj M.val) ≪≫
    (PresheafOfModules.sheafification
      (𝟙 (ringCatSheaf (pushforwardCommRing (J := K) F R)).obj)).mapIso
        ((presheafPushforwardExteriorPowerIso (K := K) F n).app M.val) ≪≫
    (exteriorPowerIso n ((pushforwardModule (J := K) F R).obj M)).symm

/-- The forward map of `pushforwardExteriorPowerIso` is the sheafification--pushforward comparison
followed by the sheafified presheaf-level comparison `presheafPushforwardExteriorPowerIso`, read
through the defining identifications of the two exterior powers. -/
@[simp]
theorem pushforwardExteriorPowerIso_hom (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardExteriorPowerIso F n M).hom =
      (pushforwardModule (J := K) F R).map (exteriorPowerIso n M).hom ≫
        (pushforwardSheafificationIso F (ringCatSheaf R)
          ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj M.val)).hom ≫
        (PresheafOfModules.sheafification
          (𝟙 (ringCatSheaf (pushforwardCommRing (J := K) F R)).obj)).map
            ((presheafPushforwardExteriorPowerIso (K := K) F n).hom.app M.val) ≫
        (exteriorPowerIso n ((pushforwardModule (J := K) F R).obj M)).inv :=
  -- `Iso.trans_hom` does not fire: as for `pushforwardTensorProductIso_hom`, the coefficient
  -- sheaves of the middle isomorphisms agree with the outer ones only up to unfolding
  (rfl)

/-- `pushforwardSheafificationIso`, as a natural isomorphism of functors on presheaves of
modules. -/
private def pushforwardSheafificationNatIso :
    PresheafOfModules.sheafification (R₀ := (ringCatSheaf R).obj) (R := ringCatSheaf R) (𝟙 _) ⋙
        pushforwardModule (J := K) F R ≅
      PresheafOfModules.pushforward (F := F) (pushforwardRingIso (J := K) F (ringCatSheaf R)).inv ⋙
        PresheafOfModules.sheafification
          (R := (F.sheafPushforwardContinuous RingCat K J).obj (ringCatSheaf R)) (𝟙 _) :=
  (NatIso.ofComponents (fun P ↦ (pushforwardSheafificationIso F (ringCatSheaf R) P).symm)
    (fun f ↦ pushforwardSheafificationIso_inv_naturality F (ringCatSheaf R) f)).symm

/-- `pushforwardExteriorPowerIso`, assembled as a natural isomorphism from the natural
sheafification--pushforward comparison and the sheafified `presheafPushforwardExteriorPowerIso`.
Its components are `pushforwardExteriorPowerIso` (`pushforwardExteriorPowerIso_hom_eq`). -/
private def pushforwardExteriorPowerNatIso (n : ℕ) :
    exteriorPower R n ⋙ pushforwardModule (J := K) F R ≅
      pushforwardModule (J := K) F R ⋙ exteriorPower (pushforwardCommRing (J := K) F R) n :=
  Functor.isoWhiskerLeft (SheafOfModules.forget (ringCatSheaf R) ⋙
      PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n)
      (pushforwardSheafificationNatIso F) ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft (SheafOfModules.forget (ringCatSheaf R))
      (presheafPushforwardExteriorPowerIso (K := K) F n))
      (PresheafOfModules.sheafification
        (R₀ := (ringCatSheaf (pushforwardCommRing (J := K) F R)).obj)
        (R := ringCatSheaf (pushforwardCommRing (J := K) F R)) (𝟙 _))

private theorem pushforwardExteriorPowerIso_hom_eq (n : ℕ)
    (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (pushforwardExteriorPowerIso F n M).hom =
      (pushforwardExteriorPowerNatIso (K := K) F n).hom.app M :=
  (rfl)

/-- `pushforwardExteriorPowerIso` is natural in the sheaf of modules. -/
@[reassoc]
theorem pushforwardExteriorPowerIso_hom_naturality (n : ℕ)
    {M N : SheafOfModules.{u} (ringCatSheaf R)} (φ : M ⟶ N) :
    (pushforwardModule (J := K) F R).map ((exteriorPower R n).map φ) ≫
        (pushforwardExteriorPowerIso F n N).hom =
      (pushforwardExteriorPowerIso F n M).hom ≫
        (exteriorPower (pushforwardCommRing (J := K) F R) n).map
          ((pushforwardModule (J := K) F R).map φ) := by
  rw [pushforwardExteriorPowerIso_hom_eq, pushforwardExteriorPowerIso_hom_eq]
  exact (pushforwardExteriorPowerNatIso (K := K) F n).hom.naturality φ

/-- For each object `X` of the site, the restriction of `⋀ⁿ M` to the slice site over `X` is the
`n`-th exterior power of the restriction of `M`. -/
def overExteriorPowerIso (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) (X : C)
    [(J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ((exteriorPower R n).obj M).over X ≅ (exteriorPower (R.over X) n).obj (M.over X) :=
  pushforwardExteriorPowerIso (K := J.over X) (Over.forget X) n M

/-- The forward map of `overExteriorPowerIso` is the slice-site instance of
`pushforwardExteriorPowerIso_hom`. -/
@[simp]
theorem overExteriorPowerIso_hom (n : ℕ) (M : SheafOfModules.{u} (ringCatSheaf R)) (X : C)
    [(J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (overExteriorPowerIso n M X).hom =
      (pushforwardExteriorPowerIso (K := J.over X) (Over.forget X) n M).hom :=
  (rfl)

/-- `overExteriorPowerIso` is natural in the sheaf of modules. -/
@[reassoc]
theorem overExteriorPowerIso_hom_naturality (n : ℕ) {M N : SheafOfModules.{u} (ringCatSheaf R)}
    (φ : M ⟶ N) (X : C)
    [(J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ((exteriorPower R n).map φ).over X ≫ (overExteriorPowerIso n N X).hom =
      (overExteriorPowerIso n M X).hom ≫ (exteriorPower (R.over X) n).map (φ.over X) :=
  pushforwardExteriorPowerIso_hom_naturality (K := J.over X) (Over.forget X) n φ

end Pushforward

end SheafOfModules

end
