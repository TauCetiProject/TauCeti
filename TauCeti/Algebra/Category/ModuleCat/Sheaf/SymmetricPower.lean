/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.SymmetricPower

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
* `SheafOfModules.symmetricPowerOneIso` identifies `Sym¹ M` with `M`.
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

end SheafOfModules

end
