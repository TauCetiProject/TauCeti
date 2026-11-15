/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Module localization and extension of scalars

For a commutative ring `R` and a submonoid `T` of `R`, Mathlib's
`ModuleCat.localizedModuleFunctor T` sends an `R`-module `M` to the shrunk localized module
`Shrink (LocalizedModule T M)`. When `M` lives in the same universe as `R`, unshrinking identifies
`M.localizedModule T` with `LocalizedModule T M` (`ModuleCat.localizedModuleIso`), and composing
with `ModuleCat.extendScalarsLocalizationIso` gives a natural isomorphism
`ModuleCat.localizedModuleFunctor T ≅ ModuleCat.extendScalars (algebraMap R (Localization T))`
(`ModuleCat.localizedModuleFunctorIsoExtendScalars`). In particular, extension of scalars to a
localization preserves finite limits.
-/

public section

universe u

namespace ModuleCat

open CategoryTheory Limits
open scoped TensorProduct ChangeOfRings

variable {R : Type u} [CommRing R]

/-- When `M` lives in the universe of `R`, unshrinking identifies `M.localizedModule T` with
`LocalizedModule T M` as `Localization T`-modules. -/
noncomputable def localizedModuleIso (M : ModuleCat.{u} R) (T : Submonoid R) :
    M.localizedModule T ≅ of (Localization T) (LocalizedModule T M) :=
  (Shrink.linearEquiv.{u} (Localization T) (LocalizedModule T M)).toModuleIso

/-- `localizedModuleIso` sends `M.localizedModuleMkLinearMap T m` to `LocalizedModule.mk m 1`. -/
@[simp]
theorem localizedModuleIso_hom_mkLinearMap (M : ModuleCat.{u} R) (T : Submonoid R) (m : M) :
    (M.localizedModuleIso T).hom (M.localizedModuleMkLinearMap T m) = LocalizedModule.mk m 1 :=
  -- `localizedModuleIso` unshrinks via `(equivShrink _).symm`, while `localizedModuleMkLinearMap`
  -- shrinks `LocalizedModule.mk m 1` via `equivShrink _`.
  (equivShrink (LocalizedModule T M)).symm_apply_apply (LocalizedModule.mk m 1)

/-- The inverse of `localizedModuleIso` sends `m / t` to
`(1 / t) • localizedModuleMkLinearMap m`. -/
@[simp]
theorem localizedModuleIso_inv_mk (M : ModuleCat.{u} R) (T : Submonoid R) (m : M) (t : T) :
    (M.localizedModuleIso T).inv (LocalizedModule.mk m t) =
      Localization.mk 1 t • M.localizedModuleMkLinearMap T m := by
  apply (ConcreteCategory.bijective_of_isIso (M.localizedModuleIso T).hom).1
  have h : Localization.mk 1 t • (LocalizedModule.mk m 1 : LocalizedModule T M) =
      LocalizedModule.mk m t := by
    simpa using LocalizedModule.mk_smul_mk (R := R) (S := T) 1 m t 1
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply, map_smul,
    localizedModuleIso_hom_mkLinearMap, h]

/-- Naturality of `M.localizedModuleIso T ≪≫ (M.extendScalarsLocalizationIso T).symm`. -/
private theorem localizedModuleMap_comp_extendScalarsLocalizationIso
    (T : Submonoid R) {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    localizedModuleMap T f ≫
        (N.localizedModuleIso T).hom ≫ (N.extendScalarsLocalizationIso T).inv =
      ((M.localizedModuleIso T).hom ≫ (M.extendScalarsLocalizationIso T).inv) ≫
        (extendScalars (algebraMap R (Localization T))).map f := by
  rw [← cancel_mono (N.extendScalarsLocalizationIso T).hom]
  ext x
  have key :
      ((localizedModuleMap T f ≫
          (N.localizedModuleIso T).hom ≫
          (N.extendScalarsLocalizationIso T).inv) ≫
          (N.extendScalarsLocalizationIso T).hom).hom.restrictScalars R =
        (((M.localizedModuleIso T).hom ≫ (M.extendScalarsLocalizationIso T).inv) ≫
          (extendScalars (algebraMap R (Localization T))).map f ≫
          (N.extendScalarsLocalizationIso T).hom).hom.restrictScalars R := by
    refine IsLocalizedModule.ext T (M.localizedModuleMkLinearMap T)
      (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap T N)) ?_
    ext m
    have hmap :
        (localizedModuleMap T f) (M.localizedModuleMkLinearMap T m) =
          N.localizedModuleMkLinearMap T (f m) :=
      IsLocalizedModule.map_apply T (M.localizedModuleMkLinearMap T)
        (N.localizedModuleMkLinearMap T) f.hom m
    -- Evaluate `restrictScalars` and linear composition as `ModuleCat` morphism application.
    change ((localizedModuleMap T f ≫
        (N.localizedModuleIso T).hom ≫
        (N.extendScalarsLocalizationIso T).inv) ≫
        (N.extendScalarsLocalizationIso T).hom) (M.localizedModuleMkLinearMap T m) =
      (((M.localizedModuleIso T).hom ≫ (M.extendScalarsLocalizationIso T).inv) ≫
        (extendScalars (algebraMap R (Localization T))).map f ≫
        (N.extendScalarsLocalizationIso T).hom) (M.localizedModuleMkLinearMap T m)
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, ConcreteCategory.comp_apply,
      hmap]
    rw [localizedModuleIso_hom_mkLinearMap, localizedModuleIso_hom_mkLinearMap,
      extendScalarsLocalizationIso_inv_mk_one]
    -- `ExtendScalars.map_tmul` acts on the underlying tensor product type of `extendScalars`.
    erw [ExtendScalars.map_tmul, extendScalarsLocalizationIso_hom_one_tmul]
  exact congr($key x)

/-- Module localization at `T` is naturally isomorphic to extension of scalars along
`R → Localization T`. -/
noncomputable def localizedModuleFunctorIsoExtendScalars (T : Submonoid R) :
    localizedModuleFunctor.{u} T ≅ extendScalars (algebraMap R (Localization T)) :=
  NatIso.ofComponents
    (fun M ↦
      (M.localizedModuleIso T : (localizedModuleFunctor.{u} T).obj M ≅ _) ≪≫
        (M.extendScalarsLocalizationIso T).symm)
    (fun f ↦ localizedModuleMap_comp_extendScalarsLocalizationIso T f)

/-- Forward component of `localizedModuleFunctorIsoExtendScalars`. -/
@[simp]
theorem localizedModuleFunctorIsoExtendScalars_hom_app (T : Submonoid R) (M : ModuleCat.{u} R) :
    (localizedModuleFunctorIsoExtendScalars T).hom.app M =
      (M.localizedModuleIso T).hom ≫ (M.extendScalarsLocalizationIso T).inv :=
  (rfl)

/-- Inverse component of `localizedModuleFunctorIsoExtendScalars`. -/
@[simp]
theorem localizedModuleFunctorIsoExtendScalars_inv_app (T : Submonoid R) (M : ModuleCat.{u} R) :
    (localizedModuleFunctorIsoExtendScalars T).inv.app M =
      (M.extendScalarsLocalizationIso T).hom ≫ (M.localizedModuleIso T).inv :=
  (rfl)

/-- Extension of scalars to a localization preserves finite limits, since localization is flat. -/
instance preservesFiniteLimits_extendScalars_localization (T : Submonoid R) :
    PreservesFiniteLimits (extendScalars.{u, u, u} (algebraMap R (Localization T))) :=
  preservesFiniteLimits_of_natIso (localizedModuleFunctorIsoExtendScalars T)

end ModuleCat
