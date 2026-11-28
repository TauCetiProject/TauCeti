/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Module localization and extension of scalars

For a commutative ring `R` and a submonoid `T` of `R`, Mathlib's
`ModuleCat.localizedModuleFunctor T` sends an `R`-module `M` to the shrunk localized module
`Shrink (LocalizedModule T M)`. When `M` lives in a universe `max u v` at least that of `R`,
unshrinking identifies `M.localizedModule T` with `LocalizedModule T M`
(`ModuleCat.localizedModuleIso`), and composing with `ModuleCat.extendScalarsLocalizationIso` gives
a natural isomorphism
`ModuleCat.localizedModuleFunctor T ≅ ModuleCat.extendScalars (algebraMap R (Localization T))`
(`ModuleCat.localizedModuleFunctorIsoExtendScalars`). In particular, extension of scalars to a
localization preserves finite limits.

For localization away from a single element `f`, `toLocalizedModuleZPow f n` sends `x` to
`fⁿ • (x/1)` for any integer `n`. Its image is the copy of `fⁿ M` in `M[1/f]` used to
describe the terms of a décalage complex.
-/

public section

universe u v

namespace ModuleCat

open CategoryTheory Limits
open scoped TensorProduct ChangeOfRings

variable {R : Type u} [CommRing R]

/-- For `M : ModuleCat.{max u v} R`, unshrinking identifies `M.localizedModule T` with
`LocalizedModule T M` as `Localization T`-modules. -/
noncomputable def localizedModuleIso (M : ModuleCat.{max u v} R) (T : Submonoid R) :
    M.localizedModule T ≅ of (Localization T) (LocalizedModule T M) :=
  (Shrink.linearEquiv.{max u v} (Localization T) (LocalizedModule T M)).toModuleIso

/-- `localizedModuleIso` sends `M.localizedModuleMkLinearMap T m` to `LocalizedModule.mk m 1`. -/
@[simp]
theorem localizedModuleIso_hom_mkLinearMap (M : ModuleCat.{max u v} R) (T : Submonoid R) (m : M) :
    (M.localizedModuleIso T).hom (M.localizedModuleMkLinearMap T m) = LocalizedModule.mk m 1 :=
  -- `localizedModuleIso` unshrinks via `(equivShrink _).symm`, while `localizedModuleMkLinearMap`
  -- shrinks `LocalizedModule.mk m 1` via `equivShrink _`.
  (equivShrink (LocalizedModule T M)).symm_apply_apply (LocalizedModule.mk m 1)

/-- The inverse of `localizedModuleIso` sends `m / t` to
`(1 / t) • localizedModuleMkLinearMap m`. -/
@[simp]
theorem localizedModuleIso_inv_mk (M : ModuleCat.{max u v} R) (T : Submonoid R) (m : M) (t : T) :
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
    (T : Submonoid R) {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
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
    localizedModuleFunctor.{max u v} T ≅
      extendScalars.{u, u, max u v} (algebraMap R (Localization T)) :=
  NatIso.ofComponents
    (fun M ↦
      (M.localizedModuleIso T : (localizedModuleFunctor.{max u v} T).obj M ≅ _) ≪≫
        (M.extendScalarsLocalizationIso T).symm)
    (fun f ↦ localizedModuleMap_comp_extendScalarsLocalizationIso T f)

/-- Forward component of `localizedModuleFunctorIsoExtendScalars`. -/
@[simp]
theorem localizedModuleFunctorIsoExtendScalars_hom_app (T : Submonoid R)
    (M : ModuleCat.{max u v} R) :
    (localizedModuleFunctorIsoExtendScalars T).hom.app M =
      (M.localizedModuleIso T).hom ≫ (M.extendScalarsLocalizationIso T).inv :=
  (rfl)

/-- Inverse component of `localizedModuleFunctorIsoExtendScalars`. -/
@[simp]
theorem localizedModuleFunctorIsoExtendScalars_inv_app (T : Submonoid R)
    (M : ModuleCat.{max u v} R) :
    (localizedModuleFunctorIsoExtendScalars T).inv.app M =
      (M.extendScalarsLocalizationIso T).hom ≫ (M.localizedModuleIso T).inv :=
  (rfl)

/-- Extension of scalars to a localization preserves finite limits, since localization is flat. -/
instance preservesFiniteLimits_extendScalars_localization (T : Submonoid R) :
    PreservesFiniteLimits (extendScalars.{u, u, max u v} (algebraMap R (Localization T))) :=
  preservesFiniteLimits_of_natIso (localizedModuleFunctorIsoExtendScalars.{u, v} T)

section Away

variable [Small.{v} R] (f : R)

local notation "fUnit" =>
  IsUnit.unit (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f)

/-- The natural map `M → M[1/f]` sending `x` to `fⁿ • (x/1)`. The exponent may be negative. -/
noncomputable def toLocalizedModuleZPow (n : ℤ) : 𝟭 (ModuleCat.{v} R) ⟶
    localizedModuleFunctor (.powers f) ⋙ restrictScalars (algebraMap R (Localization.Away f)) where
  app M := semilinearMapAddEquiv _ M (M.localizedModule (.powers f))
    { toFun := fun x ↦ (fUnit ^ n) • M.localizedModuleMkLinearMap (.powers f) x
      map_add' := fun x y ↦ by rw [map_add, smul_add]
      map_smul' := fun r x ↦ by
        rw [map_smul, IsScalarTower.algebraMap_smul, smul_comm] }
  naturality {M N} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    -- Evaluate restriction of scalars in the underlying localized modules.
    change (fUnit ^ n) • N.localizedModuleMkLinearMap _ (g x) =
      localizedModuleMap (.powers f) g ((fUnit ^ n) • M.localizedModuleMkLinearMap _ x)
    rw [Units.smul_def, Units.smul_def, map_smul]
    exact congrArg _ (IsLocalizedModule.map_apply (.powers f) _ _ g.hom x).symm

/-- Evaluation of the scaled localization map. -/
@[simp]
lemma toLocalizedModuleZPow_app_apply (M : ModuleCat.{v} R) (n : ℤ) (x : M) :
    dsimp% only [Functor.id_obj, Functor.comp_obj] (toLocalizedModuleZPow f n).app M x =
      (fUnit ^ n) • M.localizedModuleMkLinearMap (.powers f) x :=
  (rfl)

/-- Raising the exponent by one is equivalent to multiplying the input by `f`. -/
lemma toLocalizedModuleZPow_succ_apply (M : ModuleCat.{v} R) (n : ℤ) (x : M) :
    (toLocalizedModuleZPow f (n + 1)).app M x = (toLocalizedModuleZPow f n).app M (f • x) := by
  simp only [Functor.id_obj, Functor.comp_obj, toLocalizedModuleZPow_app_apply]
  rw [zpow_add_one, mul_smul,
    Units.smul_def fUnit, IsUnit.unit_spec, IsScalarTower.algebraMap_smul, map_smul]

/-- Scaling by any integer power of `f` embeds an `f`-torsion-free module in its localization. -/
lemma toLocalizedModuleZPow_injective {M : ModuleCat.{v} R} (h : IsSMulRegular M f) (n : ℤ) :
    Function.Injective ((toLocalizedModuleZPow f n).app M) := by
  have hι := (IsLocalizedModule.injective_iff_isRegular (.powers f)
    (M.localizedModuleMkLinearMap (.powers f))).2 (fun ⟨_, k, hk⟩ ↦ hk ▸ h.pow k)
  exact (MulAction.injective (fUnit ^ n)).comp hι

end Away

end ModuleCat
