/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.BaseChange
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars

/-!
# Change of rings

The counit of restriction of scalars along a ring equivalence, and its inverse, act as the
identity on the underlying elements.

It also records three facts about Mathlib's extension of scalars `ModuleCat.extendScalars`.

* Extension of scalars is additive.
* Extension of scalars carries multiplication by a scalar to multiplication by its image
  (`TauCeti.ModuleCat.extendScalars_map_smul_id`). This transports the curvature equations of a
  matrix factorization when its components are extended along a ring map, so the resulting
  factorization has the image potential.
* Extension of scalars to a localization `T⁻¹R` is localization: for an `R`-module `M`,
  `T⁻¹R ⊗_R M` is isomorphic to the localized module `T⁻¹M` as a `T⁻¹R`-module, by
  `s ⊗ m ↦ s • m / 1` (`ModuleCat.extendScalarsLocalizationIso`). This identifies the
  restriction of the quasi-coherent sheaf `M~` on `Spec R` to a basic open `D(r)` with the sheaf
  associated with `M_r` on `Spec R_r`.

Along the structure map `algebraMap R S` of an `R`-algebra, extension of scalars is the tensor
product `S ⊗[R] M` taken with the algebra module structure of `S`
(`ModuleCat.extendScalarsAlgebraMapIso`). An `R`-linear map `f : M → N` to an `S`-module
exhibits `N` as the base change of `M` (`IsBaseChange S f`) exactly when its adjoint
`S ⊗[R] M → N` is bijective; in that case the adjoint morphism of modules is an isomorphism
(`ModuleCat.isIso_extendRestrictScalarsAdj_homEquiv_symm_of_isBaseChange`).
-/

public section

universe u v

namespace ModuleCat

-- Mathlib's `ModuleCat` and its scalar-restriction equivalence require rings.
variable {R S : Type*} [Ring R] [Ring S]

-- Simplify before Mathlib expands the counit into scalar-restriction comparison maps.
-- The component simp lemmas alone leave their bundled linear-map composite unreduced.
/-- The counit of restriction of scalars along a ring equivalence keeps each element. -/
@[simp↓]
theorem restrictScalarsEquivalenceOfRingEquiv_counitIso_hom_app_apply (e : R ≃+* S)
    (M : ModuleCat.{v} R) (x : M) :
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).counitIso.hom.app M x = x := (rfl)

/-- The inverse counit of restriction of scalars along a ring equivalence keeps each element. -/
@[simp↓]
theorem restrictScalarsEquivalenceOfRingEquiv_counitIso_inv_app_apply (e : R ≃+* S)
    (M : ModuleCat.{v} R) (x : M) :
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).counitIso.inv.app M x = x := (rfl)

end ModuleCat

namespace ModuleCat

open CategoryTheory
open scoped ChangeOfRings

variable {S : Type u} {T : Type v} [CommRing S] [CommRing T]

/-- Extension of scalars is additive. -/
instance (f : S →+* T) : (extendScalars f).Additive where
  map_add := by
    intro M N g h
    let _ : Algebra S T := f.toAlgebra
    apply hom_ext
    exact LinearMap.baseChange_add _ _

end ModuleCat

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

end TauCeti.ModuleCat

namespace TauCeti

open CategoryTheory
open scoped ChangeOfRings

section Localization

variable {R : Type u} [CommRing R] (M : _root_.ModuleCat.{u} R) (T : Submonoid R)

/-- Extension of scalars to the localization `T⁻¹R` is localization: `T⁻¹R ⊗_R M` is isomorphic
to the localized module `T⁻¹M`, by `s ⊗ m ↦ s • m / 1`.

This transports `LocalizedModule.equivTensorProduct` across the `Module.compHom` structure
used by `ModuleCat.extendScalars`. -/
noncomputable def _root_.ModuleCat.extendScalarsLocalizationIso :
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
theorem _root_.ModuleCat.extendScalarsLocalizationIso_hom_one_tmul (m : M) :
    (M.extendScalarsLocalizationIso T).hom
      ((1 : Localization T) ⊗ₜ[R,algebraMap R (Localization T)] m) = LocalizedModule.mk m 1 :=
  by
    -- `ModuleCat.extendScalars` uses `Module.compHom`; the tensor-product equivalence uses
    -- the algebra module structure. The congruence map identifies these presentations.
    change (LocalizedModule.equivTensorProduct T M).symm
      ((TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl (Localization T) (Localization T))
        (LinearEquiv.refl R M)) (1 ⊗ₜ[R] m)) = _
    simp

/-- The inverse of `extendScalarsLocalizationIso` sends `m / 1` to `1 ⊗ m`. -/
@[simp]
theorem _root_.ModuleCat.extendScalarsLocalizationIso_inv_mk_one (m : M) :
    (M.extendScalarsLocalizationIso T).inv (LocalizedModule.mk m 1) =
      (1 : Localization T) ⊗ₜ[R,algebraMap R (Localization T)] m :=
  by
    let i := M.extendScalarsLocalizationIso T
    -- Name the isomorphism to apply its categorical inverse identity.
    change i.inv (LocalizedModule.mk m 1) = _
    rw [← _root_.ModuleCat.extendScalarsLocalizationIso_hom_one_tmul]
    -- Evaluation of a `ModuleCat` composite is evaluation of its underlying maps.
    change (i.hom ≫ i.inv)
      ((1 : Localization T) ⊗ₜ[R,algebraMap R (Localization T)] m) = _
    erw [i.hom_inv_id, _root_.ModuleCat.id_apply]
    rfl

/-- `extendScalarsLocalizationIso` sends a pure tensor to the scalar multiple of `m / 1`. -/
@[simp]
theorem _root_.ModuleCat.extendScalarsLocalizationIso_hom_tmul (s : Localization T) (m : M) :
    (M.extendScalarsLocalizationIso T).hom
      (s ⊗ₜ[R,algebraMap R (Localization T)] m) =
      s • LocalizedModule.mk m 1 := by
  have ht := (_root_.ModuleCat.ExtendScalars.smul_tmul
    (algebraMap R (Localization T)) (M := M) s 1 m)
  rw [mul_one] at ht
  -- `erw` identifies the scalar actions through `extendScalars`'s `Module.compHom` presentation.
  exact (congrArg (fun x ↦ (M.extendScalarsLocalizationIso T).hom x) ht.symm).trans
    (by erw [map_smul, _root_.ModuleCat.extendScalarsLocalizationIso_hom_one_tmul])

/-- The inverse of `extendScalarsLocalizationIso` sends `m / t` to `t⁻¹ ⊗ m`. -/
@[simp]
theorem _root_.ModuleCat.extendScalarsLocalizationIso_inv_mk (m : M) (t : T) :
    (M.extendScalarsLocalizationIso T).inv (LocalizedModule.mk m t) =
      Localization.mk 1 t ⊗ₜ[R,algebraMap R (Localization T)] m := by
  have h : Localization.mk 1 t • LocalizedModule.mk m 1 = LocalizedModule.mk m t := by
    simpa using LocalizedModule.mk_smul_mk 1 m t 1
  rw [← h, map_smul, _root_.ModuleCat.extendScalarsLocalizationIso_inv_mk_one]
  exact (_root_.ModuleCat.ExtendScalars.smul_tmul
    (algebraMap R (Localization T)) (M := M) (Localization.mk 1 t) 1 m).trans
      (by rw [mul_one])

end Localization

section AlgebraMap

open scoped TensorProduct

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Extension of scalars along `algebraMap R S` is the tensor product `S ⊗[R] M` with the algebra
module structure of `S`. `ModuleCat.extendScalars` uses the `Module.compHom` structure of `S`;
the two tensor products are identified by the identity of `S`. -/
@[expose]
noncomputable def _root_.ModuleCat.extendScalarsAlgebraMapIso (M : _root_.ModuleCat.{u} R) :
    (_root_.ModuleCat.extendScalars (algebraMap R S)).obj M ≅ _root_.ModuleCat.of S (S ⊗[R] M) :=
  let E := (_root_.ModuleCat.restrictScalars (algebraMap R S)).obj (_root_.ModuleCat.of S S)
  have : IsScalarTower R S E := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let c : E ≃ₗ[S] S := LinearEquiv.refl S S
  let e := TensorProduct.AlgebraTensorModule.congr c (LinearEquiv.refl R M)
  { hom := _root_.ModuleCat.ofHom e.toLinearMap
    inv := _root_.ModuleCat.ofHom e.symm.toLinearMap
    hom_inv_id := _root_.ModuleCat.hom_ext (LinearMap.ext e.symm_apply_apply)
    inv_hom_id := _root_.ModuleCat.hom_ext (LinearMap.ext e.apply_symm_apply) }

/-- `extendScalarsAlgebraMapIso` sends `s ⊗ m` to `s ⊗ m`. -/
@[simp]
theorem _root_.ModuleCat.extendScalarsAlgebraMapIso_hom_tmul (M : _root_.ModuleCat.{u} R) (s : S)
    (m : M) :
    (_root_.ModuleCat.extendScalarsAlgebraMapIso M).hom (s ⊗ₜ[R, algebraMap R S] m) =
      s ⊗ₜ[R] m :=
  rfl

/-- The inverse of `extendScalarsAlgebraMapIso` sends `s ⊗ m` to `s ⊗ m`. -/
@[simp]
theorem _root_.ModuleCat.extendScalarsAlgebraMapIso_inv_tmul (M : _root_.ModuleCat.{u} R) (s : S)
    (m : M) :
    (_root_.ModuleCat.extendScalarsAlgebraMapIso M).inv (s ⊗ₜ[R] m) =
      s ⊗ₜ[R, algebraMap R S] m :=
  rfl

/-- **Base change and extension of scalars.** If an `R`-linear map `f : M → N` to an `S`-module
exhibits `N` as the base change of `M` along `R → S`, then its adjoint `S ⊗[R] M → N`,
`s ⊗ m ↦ s • f m`, is an isomorphism of `S`-modules. -/
theorem _root_.ModuleCat.isIso_extendRestrictScalarsAdj_homEquiv_symm_of_isBaseChange
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] {f : M →ₗ[R] N} (hf : IsBaseChange S f) :
    IsIso (((_root_.ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv
      (_root_.ModuleCat.of R M) (_root_.ModuleCat.of S N)).symm
        (_root_.ModuleCat.ofHom f ≫ (_root_.ModuleCat.restrictScalarsAlgebraMapIso N).inv)) := by
  have key : (_root_.ModuleCat.extendScalarsAlgebraMapIso (_root_.ModuleCat.of R M)).inv ≫
      ((_root_.ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv
        (_root_.ModuleCat.of R M) (_root_.ModuleCat.of S N)).symm
          (_root_.ModuleCat.ofHom f ≫ (_root_.ModuleCat.restrictScalarsAlgebraMapIso N).inv) =
      _root_.ModuleCat.ofHom hf.equiv.toLinearMap := by
    refine _root_.ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
    induction z using TensorProduct.inductionOn with
    | tmul s m =>
      rw [_root_.ModuleCat.hom_ofHom, LinearEquiv.coe_coe, IsBaseChange.equiv_tmul,
        _root_.ModuleCat.hom_comp, LinearMap.comp_apply,
        _root_.ModuleCat.extendScalarsAlgebraMapIso_inv_tmul]
      -- The adjoint of a morphism into a restriction of scalars is Mathlib's
      -- `fromExtendScalars`, which sends `s ⊗ m` to `s • f m`.
      change (_root_.ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (algebraMap R S) (Y := _root_.ModuleCat.of S N) (_root_.ModuleCat.ofHom f ≫
          (_root_.ModuleCat.restrictScalarsAlgebraMapIso N).inv)).hom
            (s ⊗ₜ[R, algebraMap R S] m) = s • f m
      erw [_root_.ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_hom_apply]
      exact congrArg (fun x : N ↦ s • x)
        (_root_.ModuleCat.restrictScalarsAlgebraMapIso_inv_apply (R := R) (S := S) N (f m))
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have : IsIso ((_root_.ModuleCat.extendScalarsAlgebraMapIso (_root_.ModuleCat.of R M)).inv ≫
      ((_root_.ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).homEquiv
        (_root_.ModuleCat.of R M) (_root_.ModuleCat.of S N)).symm
          (_root_.ModuleCat.ofHom f ≫ (_root_.ModuleCat.restrictScalarsAlgebraMapIso N).inv)) := by
    rw [key]
    exact hf.equiv.toModuleIso.isIso_hom
  exact IsIso.of_isIso_comp_left (_root_.ModuleCat.extendScalarsAlgebraMapIso _).inv _

end AlgebraMap

end TauCeti
