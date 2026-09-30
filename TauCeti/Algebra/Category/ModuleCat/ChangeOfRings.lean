/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.Module

/-!
# Extension of scalars

This file records two facts about Mathlib's extension of scalars `ModuleCat.extendScalars`.

* Extension of scalars carries multiplication by a scalar to multiplication by its image
  (`TauCeti.ModuleCat.extendScalars_map_smul_id`). This transports the curvature equations of a
  matrix factorization when its components are extended along a ring map, so the resulting
  factorization has the image potential.
* Extension of scalars to a localization `T⁻¹R` is localization: for an `R`-module `M`,
  `T⁻¹R ⊗_R M` is isomorphic to the localized module `T⁻¹M` as a `T⁻¹R`-module, by
  `s ⊗ m ↦ s • m / 1` (`TauCeti.ModuleCat.extendScalarsLocalizationIso`). This identifies the
  restriction of the quasi-coherent sheaf `M~` on `Spec R` to a basic open `D(r)` with the sheaf
  associated with `M_r` on `Spec R_r`.
-/

public section

universe u v

namespace TauCeti.ModuleCat

open CategoryTheory
open scoped ChangeOfRings

section SMul

variable {S : Type u} {T : Type v} [CommRing S] [CommRing T] {w : S}

/-- Scalar extension sends multiplication by a scalar to multiplication by its image. -/
@[simp] theorem extendScalars_map_smul_id (f : S →+* T) (M : _root_.ModuleCat.{u} S) :
    (_root_.ModuleCat.extendScalars f).map (w • 𝟙 M) = f w • 𝟙 _ := by
  let _ : Algebra S T := f.toAlgebra
  apply _root_.ModuleCat.hom_ext
  -- Expose the underlying base-changed linear map after forgetting the category wrapper.
  change (w • (LinearMap.id : M →ₗ[S] M)).baseChange T =
    (f w) • (LinearMap.id : TensorProduct S T M →ₗ[T] TensorProduct S T M)
  rw [LinearMap.baseChange_smul, LinearMap.baseChange_id]
  rfl

end SMul

section Localization

variable {R : Type u} [CommRing R] (T : Submonoid R) (M : _root_.ModuleCat.{u} R)

/-- Extension of scalars to the localization `T⁻¹R` is localization: `T⁻¹R ⊗_R M` is isomorphic
to the localized module `T⁻¹M`, by `s ⊗ m ↦ s • m / 1`.

This is the `ModuleCat` form of `IsLocalizedModule.isBaseChange`; that linear equivalence cannot be
used directly because `ModuleCat.extendScalars` tensors over the `R`-module structure on `T⁻¹R`
obtained from `Module.compHom`, not over the one of the `R`-algebra `T⁻¹R`. -/
noncomputable def extendScalarsLocalizationIso :
    (_root_.ModuleCat.extendScalars (algebraMap R (Localization T))).obj M ≅
      _root_.ModuleCat.of (Localization T) (LocalizedModule T M) := by
  let φ := algebraMap R (Localization T)
  let E := (_root_.ModuleCat.extendScalars φ).obj M
  let Q := (_root_.ModuleCat.restrictScalars φ).obj E
  have : IsScalarTower R (Localization T) Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have h (x : T) : IsUnit (algebraMap R (Module.End R Q) x) := by
    rw [Module.End.isUnit_iff]
    exact (IsLocalization.map_units (Localization T) x).smul_bijective (β := E)
  -- The inverse sends `m / s` to `s⁻¹ • (1 ⊗ m)`: it is the lift of `m ↦ 1 ⊗ m` along the
  -- localization map, which is `T⁻¹R`-linear because `T⁻¹R ⊗_R M` is a `T⁻¹R`-module.
  let g : LocalizedModule T M →ₗ[Localization T] Q :=
    LinearMap.extendScalarsOfIsLocalization T (Localization T)
      (LocalizedModule.lift T ((_root_.ModuleCat.extendRestrictScalarsAdj φ).unit.app M).hom h)
  let u : M →ₛₗ[φ] LocalizedModule T M :=
    { toFun := LocalizedModule.mkLinearMap T M
      map_add' := map_add _
      map_smul' := fun r m ↦ by simp [φ, algebraMap_smul] }
  let f : E ⟶ _root_.ModuleCat.of _ (LocalizedModule T M) :=
    ((_root_.ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm
      (_root_.ModuleCat.semilinearMapAddEquiv φ M (_root_.ModuleCat.of _ (LocalizedModule T M)) u)
  have hf (m : M) : f ((1 : Localization T) ⊗ₜ[R,φ] m) = LocalizedModule.mk m 1 :=
    ConcreteCategory.congr_hom
      ((_root_.ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _ |>.apply_symm_apply _) m
  have hg (m : M) : g (LocalizedModule.mk m 1) = (1 : Localization T) ⊗ₜ[R,φ] m := by
    simp only [g, LinearMap.extendScalarsOfIsLocalization_apply', LocalizedModule.lift_mk_one]
    exact _root_.ModuleCat.extendRestrictScalarsAdj_unit_app_apply φ M m
  exact
    { hom := f
      inv := _root_.ModuleCat.ofHom (Y := E) g
      hom_inv_id := by
        ext m
        exact (congrArg g (hf m)).trans (hg m)
      inv_hom_id := by
        ext : 1
        apply LinearMap.restrictScalars_injective R
        apply IsLocalizedModule.ext T (LocalizedModule.mkLinearMap T M)
          (IsLocalizedModule.map_units (LocalizedModule.mkLinearMap T M))
        ext m
        exact (congrArg f (hg m)).trans (hf m) }

/-- `extendScalarsLocalizationIso` sends `1 ⊗ m` to `m / 1`. -/
@[simp]
theorem extendScalarsLocalizationIso_hom_one_tmul (m : M) :
    (extendScalarsLocalizationIso T M).hom
      ((1 : Localization T) ⊗ₜ[R,algebraMap R (Localization T)] m) = LocalizedModule.mk m 1 :=
  ConcreteCategory.congr_hom
    ((_root_.ModuleCat.extendRestrictScalarsAdj _).homEquiv _ _ |>.apply_symm_apply _) m

/-- The inverse of `extendScalarsLocalizationIso` sends `m / 1` to `1 ⊗ m`. -/
@[simp]
theorem extendScalarsLocalizationIso_inv_mk (m : M) :
    (extendScalarsLocalizationIso T M).inv (LocalizedModule.mk m 1) =
      (1 : Localization T) ⊗ₜ[R,algebraMap R (Localization T)] m :=
  (congrArg (extendScalarsLocalizationIso T M).inv
    (extendScalarsLocalizationIso_hom_one_tmul T M m)).symm.trans (Iso.hom_inv_id_apply _ _)

end Localization

end TauCeti.ModuleCat
