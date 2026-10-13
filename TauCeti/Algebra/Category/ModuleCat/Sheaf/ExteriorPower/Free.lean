/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Exterior powers of free sheaves of modules

Let `R` be a sheaf of commutative rings on a small site. If `I` is a finite linearly ordered type,
the `n`-th exterior power of the free sheaf of `R`-modules on `I` is free on the set
`Set.powersetCard I n` of `n`-element subsets of `I`: over each object `W`, the sections of
`free I` form a free `R(W)`-module with basis the sections `eᵢ = freeSection i`
(`TauCeti.SheafOfModules.freeBasis`), so their `n`-th exterior power is free with basis the
wedge products `e_{i₁} ∧ ⋯ ∧ e_{iₙ}` for `i₁ < ⋯ < iₙ` (Mathlib's `Module.Basis.exteriorPower`).
These bases are preserved by the restriction maps, so they identify the sectionwise exterior
power of `free I` with the underlying presheaf of `free (Set.powersetCard I n)`, and sheafifying
gives `⋀ⁿ (free I) ≅ free (Set.powersetCard I n)`.

## Main declarations

* `SheafOfModules.presheafExteriorPowerFreeIso`: the sectionwise exterior power of `free I` is
  the underlying presheaf of `free (Set.powersetCard I n)`, sending the wedge product of the
  basis sections indexed by `s` to the basis section indexed by `s`
  (`presheafExteriorPowerFreeIso_hom_app_ιMulti_family`);
* `SheafOfModules.exteriorPowerFreeIso`: `⋀ⁿ (free I) ≅ free (Set.powersetCard I n)`.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 5.16
-/

public section

open CategoryTheory
open TauCeti.SheafOfModules (ringCatSheaf freeBasis freeBasis_map)

universe u

noncomputable section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}}

namespace SheafOfModules

variable (I : Type u) [Finite I] [LinearOrder I]

/-- The sectionwise `n`-th exterior power of the free sheaf of modules on a finite linearly
ordered type `I` is the underlying presheaf of the free sheaf on the `n`-element subsets of `I`:
over each object `W` it maps the basis of `⋀[R(W)]^n` induced by `freeBasis I W` to
`freeBasis (Set.powersetCard I n) W`. -/
def presheafExteriorPowerFreeIso (n : ℕ) :
    (PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj
        (free (R := ringCatSheaf R) I).val ≅
      (free (R := ringCatSheaf R) (Set.powersetCard I n)).val :=
  PresheafOfModulesOfCommRing.isoMk
    (fun W ↦ (((freeBasis (R := R) I W).exteriorPower n).equiv
      (freeBasis (R := R) _ W) (Equiv.refl _)).toModuleIso)
    (fun W W' f ↦ by
      ext : 1
      refine ((freeBasis (R := R) I W).exteriorPower n).ext fun s ↦ ?_
      -- Restriction sends the wedge product of basis sections indexed by `s` over `W` to the one
      -- over `W'`, since it preserves the basis sections of `free I`.
      have hP : ((PresheafOfModulesOfCommRing.exteriorPower (R := R.obj) n).obj
          (free (R := ringCatSheaf R) I).val).map f
            ((freeBasis (R := R) I W).exteriorPower n s) =
          (freeBasis (R := R) I W').exteriorPower n s := by
        rw [exteriorPower.basis_apply, exteriorPower.basis_apply]
        exact (PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk n _ f _).trans
          (congrArg _ (funext fun j ↦ freeBasis_map I f _))
      -- Both sides send this wedge product to the basis section indexed by `s` over `W'`.
      exact ((congrArg (((freeBasis (R := R) I W').exteriorPower n).equiv
          (freeBasis (R := R) _ W') (Equiv.refl _)) hP).trans
            (Module.Basis.equiv_apply _ _ _ _)).trans
        ((congrArg ((free (R := ringCatSheaf R) (Set.powersetCard I n)).val.map f)
          (Module.Basis.equiv_apply _ _ _ _)).trans (freeBasis_map _ f s)).symm)

/-- `presheafExteriorPowerFreeIso` sends the wedge product, in increasing order, of the basis
sections of `free I` indexed by an `n`-element subset `s` to the basis section indexed by `s`. -/
theorem presheafExteriorPowerFreeIso_hom_app_ιMulti_family (n : ℕ) (W : Cᵒᵖ)
    (s : Set.powersetCard I n) :
    (presheafExteriorPowerFreeIso (R := R) I n).hom.app W
        (exteriorPower.ιMulti_family (R.obj.obj W) n
          (fun i ↦ (freeSection (R := ringCatSheaf R) i).eval W) s) =
      (freeSection (R := ringCatSheaf R) s).eval W := by
  have h : (fun i ↦ (freeSection (R := ringCatSheaf R) i).eval W) = freeBasis (R := R) I W :=
    funext fun i ↦ (TauCeti.SheafOfModules.freeBasis_apply I W i).symm
  rw [h, ← exteriorPower.basis_apply]
  exact (Module.Basis.equiv_apply _ _ _ _).trans (TauCeti.SheafOfModules.freeBasis_apply _ W s)

/-- The inverse of `presheafExteriorPowerFreeIso` sends the basis section indexed by an
`n`-element subset `s` to the wedge product, in increasing order, of the basis sections of
`free I` indexed by `s`. -/
theorem presheafExteriorPowerFreeIso_inv_app_freeSection (n : ℕ) (W : Cᵒᵖ)
    (s : Set.powersetCard I n) :
    (presheafExteriorPowerFreeIso (R := R) I n).inv.app W
        ((freeSection (R := ringCatSheaf R) s).eval W) =
      exteriorPower.ιMulti_family (R.obj.obj W) n
        (fun i ↦ (freeSection (R := ringCatSheaf R) i).eval W) s := by
  rw [← presheafExteriorPowerFreeIso_hom_app_ιMulti_family]
  exact ((PresheafOfModules.evaluation _ W).mapIso
    (presheafExteriorPowerFreeIso (R := R) I n)).hom_inv_id_apply _

/-- The `n`-th exterior power of the free sheaf of modules on a finite linearly ordered type `I`
is the free sheaf on the `n`-element subsets of `I`. -/
def exteriorPowerFreeIso (n : ℕ) :
    (exteriorPower R n).obj (free (R := ringCatSheaf R) I) ≅
      free (R := ringCatSheaf R) (Set.powersetCard I n) :=
  exteriorPowerIso n (free I) ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso
      (presheafExteriorPowerFreeIso I n) ≪≫
    TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R) (free _)

/-- The forward map of `exteriorPowerFreeIso` is the sheafification of
`presheafExteriorPowerFreeIso`, followed by the identification of the sheafified underlying
presheaf of a free sheaf with that sheaf. -/
@[simp]
theorem exteriorPowerFreeIso_hom (n : ℕ) :
    (exteriorPowerFreeIso (R := R) I n).hom =
      (exteriorPowerIso n (free I)).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).map
          (presheafExteriorPowerFreeIso I n).hom ≫
        (TauCeti.SheafOfModules.sheafificationIso (ringCatSheaf R) (free _)).hom :=
  (rfl)

end SheafOfModules

end
