/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.BaseChange

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

variable {R : Type u} [CommRing R] (M : _root_.ModuleCat.{u} R) (T : Submonoid R)

/-- Extension of scalars to the localization `T⁻¹R` is localization: `T⁻¹R ⊗_R M` is isomorphic
to the localized module `T⁻¹M`, by `s ⊗ m ↦ s • m / 1`.

This transports `LocalizedModule.equivTensorProduct` across the `Module.compHom` structure
used by `ModuleCat.extendScalars`. -/
noncomputable def extendScalarsLocalizationIso :
    (_root_.ModuleCat.extendScalars (algebraMap R (Localization T))).obj M ≅
      _root_.ModuleCat.of (Localization T) (LocalizedModule T M) := by
  let φ := algebraMap R (Localization T)
  let A := Localization T
  let E := (_root_.ModuleCat.restrictScalars φ).obj (_root_.ModuleCat.of A A)
  have : IsScalarTower R A E := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let c : E ≃ₗ[A] A := LinearEquiv.refl A A
  let b := TensorProduct.AlgebraTensorModule.congr c (LinearEquiv.refl R M)
  let e := b.trans (LocalizedModule.equivTensorProduct T M).symm
  exact
    { hom := _root_.ModuleCat.ofHom e.toLinearMap
      inv := _root_.ModuleCat.ofHom e.symm.toLinearMap
      hom_inv_id := by
        apply _root_.ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact e.symm_apply_apply x
      inv_hom_id := by
        apply _root_.ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact e.apply_symm_apply x }

/-- `extendScalarsLocalizationIso` sends `1 ⊗ m` to `m / 1`. -/
@[simp]
theorem extendScalarsLocalizationIso_hom_one_tmul (m : M) :
    (extendScalarsLocalizationIso M T).hom
      ((1 : Localization T) ⊗ₜ[R,algebraMap R (Localization T)] m) = LocalizedModule.mk m 1 :=
  by
    change (LocalizedModule.equivTensorProduct T M).symm
      ((TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (Localization T) (Localization T))
        (LinearEquiv.refl R M)) (1 ⊗ₜ[R] m)) = _
    simp

/-- The inverse of `extendScalarsLocalizationIso` sends `m / 1` to `1 ⊗ m`. -/
@[simp]
theorem extendScalarsLocalizationIso_inv_mk_one (m : M) :
    (extendScalarsLocalizationIso M T).inv (LocalizedModule.mk m 1) =
      (1 : Localization T) ⊗ₜ[R,algebraMap R (Localization T)] m :=
  by
    let φ := algebraMap R (Localization T)
    let E := (_root_.ModuleCat.restrictScalars φ).obj
      (_root_.ModuleCat.of (Localization T) (Localization T))
    have : IsScalarTower R (Localization T) E :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let c : E ≃ₗ[Localization T] Localization T := LinearEquiv.refl _ _
    change ((LocalizedModule.equivTensorProduct T M).trans
      (TensorProduct.AlgebraTensorModule.congr c (LinearEquiv.refl R M)).symm)
      (LocalizedModule.mk m 1) = _
    simp only [LinearEquiv.trans_apply, LocalizedModule.equivTensorProduct_apply_mk]
    rw [TensorProduct.AlgebraTensorModule.congr_symm_tmul]
    have hc : c.symm (Localization.mk 1 1) = (1 : Localization T) := by
      change Localization.mk 1 1 = 1
      exact Localization.mk_one
    rw [hc]
    rfl

/-- `extendScalarsLocalizationIso` sends a pure tensor to the scalar multiple of `m / 1`. -/
@[simp]
theorem extendScalarsLocalizationIso_hom_tmul (s : Localization T) (m : M) :
    (extendScalarsLocalizationIso M T).hom
      (s ⊗ₜ[R,algebraMap R (Localization T)] m) =
      s • LocalizedModule.mk m 1 := by
  rfl

/-- The inverse of `extendScalarsLocalizationIso` sends `m / t` to `t⁻¹ ⊗ m`. -/
@[simp]
theorem extendScalarsLocalizationIso_inv_mk (m : M) (t : T) :
    (extendScalarsLocalizationIso M T).inv (LocalizedModule.mk m t) =
      Localization.mk 1 t ⊗ₜ[R,algebraMap R (Localization T)] m := by
  have h : Localization.mk 1 t • LocalizedModule.mk m 1 = LocalizedModule.mk m t := by
    simpa using LocalizedModule.mk_smul_mk 1 m t 1
  rw [← h, map_smul, extendScalarsLocalizationIso_inv_mk_one]
  exact (_root_.ModuleCat.ExtendScalars.smul_tmul
    (algebraMap R (Localization T)) (M := M) (Localization.mk 1 t) 1 m).trans
      (by rw [mul_one])

end Localization

end TauCeti.ModuleCat
