/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower

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
* `SheafOfModules.exteriorPowerOneIso` identifies `⋀¹ M` with `M`.
-/

public section

open CategoryTheory
open TauCeti.SheafOfModules (ringCatSheaf)

universe u v₁ u₁

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

end SheafOfModules

end
