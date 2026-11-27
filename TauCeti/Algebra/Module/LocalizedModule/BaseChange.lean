/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Base change and scalar restriction for localized modules

Let `R → A` be a homomorphism of commutative semirings and `T ⊆ R` a multiplicative submonoid
with image `Algebra.algebraMapSubmonoid A T` in `A`.

First, base change along `R → A` preserves module localization: if `f : M →ₗ[R] M'` localizes `M`
at `T`, then `f.baseChange A : A ⊗[R] M →ₗ[A] A ⊗[R] M'` localizes `A ⊗[R] M` at the image of
`T` (`IsLocalizedModule.baseChange`). Applying this to `LocalizedModule.mkLinearMap T M` identifies
`A ⊗[R] LocalizedModule T M` with `LocalizedModule (Algebra.algebraMapSubmonoid A T) (A ⊗[R] M)`
naturally in `M` (`LocalizedModule.baseChangeEquiv`). Consequently, surjectivity and bijectivity
of `LocalizedModule.map T f` pass to
`LocalizedModule.map (Algebra.algebraMapSubmonoid A T) (f.baseChange A)` without flatness
assumptions on `A`, while injectivity passes when `A` is flat over `R`. When `A` is itself a
localization of `R` at `T`, these properties hold for `f.baseChange A` itself if and only if they
hold for `LocalizedModule.map T f`.

Second, for an `A`-linear map `g : P₁ →ₗ[A] P₂`, localizing at `Algebra.algebraMapSubmonoid A T`
agrees with localizing `g.restrictScalars R` at `T`, so injectivity, surjectivity, and bijectivity
of the two localized maps are equivalent, and the underlying localized modules are canonically
`R`-linearly isomorphic (`LocalizedModule.restrictScalarsEquiv`, naturally via
`LocalizedModule.restrictScalarsEquiv_map_apply`).

## Main declarations

* `IsLocalizedModule.baseChange`: scalar extension of a localization map is a localization map at
  the image submonoid.
* `LocalizedModule.baseChangeEquiv`: the natural `A`-linear equivalence
  `A ⊗[R] LocalizedModule T M ≃ₗ[A] LocalizedModule (Algebra.algebraMapSubmonoid A T) (A ⊗[R] M)`.
* `LocalizedModule.map_baseChange_surjective`, `LocalizedModule.map_baseChange_bijective`,
  `LocalizedModule.map_baseChange_injective`: preservation of surjectivity, bijectivity, and
  (under flatness) injectivity of localized maps under base change.
* `LocalizedModule.restrictScalarsEquiv`, `LocalizedModule.restrictScalarsEquiv_map_apply`: the
  natural `R`-linear equivalence
  `LocalizedModule T P ≃ₗ[R] LocalizedModule (Algebra.algebraMapSubmonoid A T) P` for an
  `A`-module `P`, together with equivalences for injectivity, surjectivity, and bijectivity of
  localized maps.
* `LocalizedModule.tensorProductEquivOfEquiv`, `LocalizedModule.tensorProductEquivOfEquiv_apply`:
  an equivalence `T⁻¹M ≃ T⁻¹N` of localized modules
  as the corresponding equivalence `T⁻¹R ⊗[R] M ≃ T⁻¹R ⊗[R] N` of scalar extensions.
* `IsLocalization.baseChange_injective_iff`, `IsLocalization.baseChange_surjective_iff`,
  `IsLocalization.baseChange_bijective_iff`: when `A` is a localization of `R` at `T`,
  injectivity, surjectivity, and bijectivity of `f.baseChange A` coincide with those of
  `LocalizedModule.map T f`.
-/

public section

open Function TensorProduct

section IsLocalizedModule

variable {R : Type*} [CommSemiring R] (T : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A]
  {M M' : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

/-- Base change along `R → A` sends a localization map at `T` to a localization map at the image
submonoid `Algebra.algebraMapSubmonoid A T`. -/
instance IsLocalizedModule.baseChange (f : M →ₗ[R] M') [IsLocalizedModule T f] :
    IsLocalizedModule (Algebra.algebraMapSubmonoid A T) (f.baseChange A) := by
  rw [IsLocalizedModule.restrictScalars_iff]
  have hcomm : (f.baseChange A).restrictScalars R =
      (TensorProduct.comm R M' A).toLinearMap ∘ₗ
        AlgebraTensorModule.rTensor R A f ∘ₗ (TensorProduct.comm R A M).toLinearMap := by
    ext a m
    rfl
  rw [hcomm, IsLocalizedModule.comp_iff_of_bijective_left T _ (TensorProduct.comm R M' A).bijective,
    IsLocalizedModule.comp_iff_of_bijective_right T _ (TensorProduct.comm R A M).bijective]
  infer_instance

end IsLocalizedModule

namespace LocalizedModule

section BaseChange

variable {R : Type*} [CommSemiring R] (T : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A]
  (M : Type*) [AddCommMonoid M] [Module R M]

/-- Base change commutes with `LocalizedModule`: extending scalars of `LocalizedModule T M` along
`R → A` is naturally isomorphic to localizing `A ⊗[R] M` at `Algebra.algebraMapSubmonoid A T`. -/
noncomputable def baseChangeEquiv :
    A ⊗[R] LocalizedModule T M ≃ₗ[A]
      LocalizedModule (Algebra.algebraMapSubmonoid A T) (A ⊗[R] M) :=
  (IsLocalizedModule.iso (Algebra.algebraMapSubmonoid A T) ((mkLinearMap T M).baseChange A)).symm

@[simp]
theorem baseChangeEquiv_tmul_mk (a : A) (m : M) (t : T) :
    baseChangeEquiv T A M (a ⊗ₜ[R] mk m t) =
      mk (a ⊗ₜ[R] m) ⟨algebraMap R A t, Algebra.mem_algebraMapSubmonoid_of_mem t⟩ := by
  refine IsLocalizedModule.iso_symm_apply' (Algebra.algebraMapSubmonoid A T)
    ((mkLinearMap T M).baseChange A) _ _ _ ?_
  rw [Submonoid.mk_smul, IsScalarTower.algebraMap_smul A (t : R), ← tmul_smul, smul'_mk,
    ← Submonoid.smul_def, mk_cancel, LinearMap.baseChange_tmul, mkLinearMap_apply]

@[simp]
theorem baseChangeEquiv_symm_mk_tmul (a : A) (m : M) (t : T) :
    (baseChangeEquiv T A M).symm
      (mk (a ⊗ₜ[R] m) ⟨algebraMap R A t, Algebra.mem_algebraMapSubmonoid_of_mem t⟩) =
      a ⊗ₜ[R] mk m t := by
  apply (baseChangeEquiv T A M).injective
  simp

variable {T A M}
variable {N : Type*} [AddCommMonoid N] [Module R N]

/-- Naturality of `LocalizedModule.baseChangeEquiv` with respect to `R`-linear maps. -/
theorem baseChangeEquiv_map_apply (f : M →ₗ[R] N) (x : A ⊗[R] LocalizedModule T M) :
    baseChangeEquiv T A N (((LocalizedModule.map T f).restrictScalars R).baseChange A x) =
      LocalizedModule.map (Algebra.algebraMapSubmonoid A T) (f.baseChange A)
        (baseChangeEquiv T A M x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a z =>
    induction z using LocalizedModule.induction_on with
    | h m t => simp
  | add x y hx hy => simp [hx, hy]

/-- Surjectivity of a localized linear map is preserved under arbitrary base change. -/
theorem map_baseChange_surjective (f : M →ₗ[R] N)
    (hf : Surjective (LocalizedModule.map T f)) :
    Surjective (LocalizedModule.map (Algebra.algebraMapSubmonoid A T) (f.baseChange A)) := by
  have hfR : Surjective ((LocalizedModule.map T f).restrictScalars R) := by
    rwa [LinearMap.coe_restrictScalars R]
  have hsurj : Surjective (((LocalizedModule.map T f).restrictScalars R).baseChange A) :=
    LinearMap.baseChange_surjective A hfR
  intro y
  obtain ⟨x, hx⟩ := hsurj ((baseChangeEquiv T A N).symm y)
  refine ⟨baseChangeEquiv T A M x, ?_⟩
  rw [← baseChangeEquiv_map_apply, hx, LinearEquiv.apply_symm_apply]

/-- Bijectivity of a localized linear map is preserved under arbitrary base change. -/
theorem map_baseChange_bijective (f : M →ₗ[R] N)
    (hf : Bijective (LocalizedModule.map T f)) :
    Bijective (LocalizedModule.map (Algebra.algebraMapSubmonoid A T) (f.baseChange A)) := by
  have hfR : Bijective ((LocalizedModule.map T f).restrictScalars R) := by
    rwa [LinearMap.coe_restrictScalars R]
  let e : LocalizedModule T M ≃ₗ[R] LocalizedModule T N :=
    LinearEquiv.ofBijective ((LocalizedModule.map T f).restrictScalars R) hfR
  have hbij : Bijective (((LocalizedModule.map T f).restrictScalars R).baseChange A) :=
    (e.baseChange R A _ _).bijective
  have hcomm : ⇑(LocalizedModule.map (Algebra.algebraMapSubmonoid A T) (f.baseChange A)) ∘
      ⇑(baseChangeEquiv T A M) =
      ⇑(baseChangeEquiv T A N) ∘ ⇑(((LocalizedModule.map T f).restrictScalars R).baseChange A) := by
    ext x
    exact (baseChangeEquiv_map_apply f x).symm
  rw [← Bijective.of_comp_iff _ (baseChangeEquiv T A M).bijective, hcomm]
  exact (baseChangeEquiv T A N).bijective.comp hbij

/-- Injectivity of a localized linear map is preserved under flat base change. -/
theorem map_baseChange_injective [Module.Flat R A] (f : M →ₗ[R] N)
    (hf : Injective (LocalizedModule.map T f)) :
    Injective (LocalizedModule.map (Algebra.algebraMapSubmonoid A T) (f.baseChange A)) := by
  have hfR : Injective ((LocalizedModule.map T f).restrictScalars R) := by
    rwa [LinearMap.coe_restrictScalars R]
  have hinj : Injective (((LocalizedModule.map T f).restrictScalars R).baseChange A) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hfR
  intro x y hxy
  apply (baseChangeEquiv T A M).symm.injective
  apply hinj
  apply (baseChangeEquiv T A N).injective
  simpa [baseChangeEquiv_map_apply] using hxy

end BaseChange

section RestrictScalars

variable {R : Type*} [CommSemiring R] (T : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A]
  (P : Type*) [AddCommMonoid P] [Module R P] [Module A P] [IsScalarTower R A P]

/-- For an `A`-module `P`, localizing `P` as an `R`-module at `T` is canonically `R`-linearly
isomorphic to localizing `P` as an `A`-module at `Algebra.algebraMapSubmonoid A T`. -/
noncomputable def restrictScalarsEquiv :
    LocalizedModule T P ≃ₗ[R] LocalizedModule (Algebra.algebraMapSubmonoid A T) P :=
  have := IsLocalizedModule.restrictScalars T
    (mkLinearMap (Algebra.algebraMapSubmonoid A T) P)
  IsLocalizedModule.iso T
    ((mkLinearMap (Algebra.algebraMapSubmonoid A T) P).restrictScalars R)

@[simp]
theorem restrictScalarsEquiv_symm_mk (x : P) (t : T) :
    (restrictScalarsEquiv T A P).symm
      (mk x ⟨algebraMap R A t, Algebra.mem_algebraMapSubmonoid_of_mem t⟩) = mk x t := by
  let U := Algebra.algebraMapSubmonoid A T
  have := IsLocalizedModule.restrictScalars T (mkLinearMap U P)
  refine IsLocalizedModule.iso_symm_apply' T ((mkLinearMap U P).restrictScalars R) _ _ _ ?_
  rw [Submonoid.smul_def, ← IsScalarTower.algebraMap_smul A (t : R), smul'_mk]
  simpa [U] using mk_cancel (⟨algebraMap R A t, Algebra.mem_algebraMapSubmonoid_of_mem t⟩ : U) x

@[simp]
theorem restrictScalarsEquiv_mk (x : P) (t : T) :
    restrictScalarsEquiv T A P (mk x t) =
      mk x ⟨algebraMap R A t, Algebra.mem_algebraMapSubmonoid_of_mem t⟩ := by
  apply (restrictScalarsEquiv T A P).symm.injective
  simp

variable {T A P}
variable {P₁ P₂ : Type*} [AddCommMonoid P₁] [Module R P₁] [Module A P₁] [IsScalarTower R A P₁]
  [AddCommMonoid P₂] [Module R P₂] [Module A P₂] [IsScalarTower R A P₂]

/-- Naturality of `LocalizedModule.restrictScalarsEquiv` with respect to `A`-linear maps. -/
theorem restrictScalarsEquiv_map_apply (g : P₁ →ₗ[A] P₂) (x : LocalizedModule T P₁) :
    restrictScalarsEquiv T A P₂ (LocalizedModule.map T (g.restrictScalars R) x) =
      LocalizedModule.map (Algebra.algebraMapSubmonoid A T) g
        (restrictScalarsEquiv T A P₁ x) := by
  induction x using LocalizedModule.induction_on with
  | h p t => simp

/-- Injectivity of `LocalizedModule.map` at `Algebra.algebraMapSubmonoid A T` is equivalent to
injectivity of `LocalizedModule.map` at `T` after restricting scalars to `R`. -/
theorem map_algebraMapSubmonoid_injective_iff (g : P₁ →ₗ[A] P₂) :
    Injective (LocalizedModule.map (Algebra.algebraMapSubmonoid A T) g) ↔
      Injective (LocalizedModule.map T (g.restrictScalars R)) := by
  have hcomm : ⇑(LocalizedModule.map (Algebra.algebraMapSubmonoid A T) g) ∘
      ⇑(restrictScalarsEquiv T A P₁) =
      ⇑(restrictScalarsEquiv T A P₂) ∘ ⇑(LocalizedModule.map T (g.restrictScalars R)) :=
    funext fun x ↦ (restrictScalarsEquiv_map_apply g x).symm
  rw [← (restrictScalarsEquiv T A P₁).toEquiv.injective_comp, LinearEquiv.coe_toEquiv, hcomm,
    ← LinearEquiv.coe_toEquiv, (restrictScalarsEquiv T A P₂).toEquiv.comp_injective]

/-- Surjectivity of `LocalizedModule.map` at `Algebra.algebraMapSubmonoid A T` is equivalent to
surjectivity of `LocalizedModule.map` at `T` after restricting scalars to `R`. -/
theorem map_algebraMapSubmonoid_surjective_iff (g : P₁ →ₗ[A] P₂) :
    Surjective (LocalizedModule.map (Algebra.algebraMapSubmonoid A T) g) ↔
      Surjective (LocalizedModule.map T (g.restrictScalars R)) := by
  have hcomm : ⇑(LocalizedModule.map (Algebra.algebraMapSubmonoid A T) g) ∘
      ⇑(restrictScalarsEquiv T A P₁) =
      ⇑(restrictScalarsEquiv T A P₂) ∘ ⇑(LocalizedModule.map T (g.restrictScalars R)) :=
    funext fun x ↦ (restrictScalarsEquiv_map_apply g x).symm
  rw [← (restrictScalarsEquiv T A P₁).toEquiv.surjective_comp, LinearEquiv.coe_toEquiv, hcomm,
    ← LinearEquiv.coe_toEquiv, (restrictScalarsEquiv T A P₂).toEquiv.comp_surjective]

/-- Bijectivity of `LocalizedModule.map` at `Algebra.algebraMapSubmonoid A T` is equivalent to
bijectivity of `LocalizedModule.map` at `T` after restricting scalars to `R`. -/
theorem map_algebraMapSubmonoid_bijective_iff (g : P₁ →ₗ[A] P₂) :
    Bijective (LocalizedModule.map (Algebra.algebraMapSubmonoid A T) g) ↔
      Bijective (LocalizedModule.map T (g.restrictScalars R)) := by
  simp only [Bijective, map_algebraMapSubmonoid_injective_iff,
    map_algebraMapSubmonoid_surjective_iff]

end RestrictScalars

section TensorProduct

variable {R : Type*} [CommSemiring R] {T : Submonoid R}
  {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- An equivalence of localized modules `T⁻¹M ≃ T⁻¹N`, transported along
`LocalizedModule.equivTensorProduct` to an equivalence of the scalar extensions
`T⁻¹R ⊗[R] M ≃ T⁻¹R ⊗[R] N`. -/
noncomputable def tensorProductEquivOfEquiv
    (e : LocalizedModule T M ≃ₗ[Localization T] LocalizedModule T N) :
    Localization T ⊗[R] M ≃ₗ[Localization T] Localization T ⊗[R] N :=
  (equivTensorProduct T M).symm ≪≫ₗ e ≪≫ₗ equivTensorProduct T N

/-- `tensorProductEquivOfEquiv e` is `e` conjugated by `LocalizedModule.equivTensorProduct`. -/
@[simp]
theorem tensorProductEquivOfEquiv_apply
    (e : LocalizedModule T M ≃ₗ[Localization T] LocalizedModule T N)
    (x : Localization T ⊗[R] M) :
    tensorProductEquivOfEquiv e x =
      equivTensorProduct T N (e ((equivTensorProduct T M).symm x)) := by
  simp [tensorProductEquivOfEquiv]

/-- The inverse of `tensorProductEquivOfEquiv e` is `e.symm` conjugated by
`LocalizedModule.equivTensorProduct`. -/
@[simp]
theorem tensorProductEquivOfEquiv_symm_apply
    (e : LocalizedModule T M ≃ₗ[Localization T] LocalizedModule T N)
    (x : Localization T ⊗[R] N) :
    (tensorProductEquivOfEquiv e).symm x =
      equivTensorProduct T M (e.symm ((equivTensorProduct T N).symm x)) := by
  simp [tensorProductEquivOfEquiv]

/-- On a pure tensor `1 ⊗ₜ m`, `tensorProductEquivOfEquiv e` applies `e` to `m / 1`. -/
theorem tensorProductEquivOfEquiv_one_tmul
    (e : LocalizedModule T M ≃ₗ[Localization T] LocalizedModule T N) (m : M) :
    tensorProductEquivOfEquiv e (1 ⊗ₜ m) =
      equivTensorProduct T N (e (LocalizedModule.mk m 1)) := by
  simp

end TensorProduct

end LocalizedModule

namespace IsLocalization

variable {R : Type*} [CommSemiring R] (T : Submonoid R)
  (A : Type*) [CommSemiring A] [Algebra R A] [IsLocalization T A]
  {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Extending an `R`-linear map along a localization `R → A` at `T` equals `IsLocalizedModule.map`
along the scalar-unit maps `TensorProduct.mk R A _ 1`. -/
theorem restrictScalars_baseChange_eq_map (f : M →ₗ[R] N) :
    (f.baseChange A).restrictScalars R =
      IsLocalizedModule.map T (TensorProduct.mk R A M 1) (TensorProduct.mk R A N 1) f := by
  apply IsLocalizedModule.linearMap_ext T
    (TensorProduct.mk R A M 1) (TensorProduct.mk R A N 1)
  rw [IsLocalizedModule.map_comp]
  ext m
  rfl

/-- Base change of `f` along a localization of `R` at `T` is injective if and only if
`LocalizedModule.map T f` is injective. -/
theorem baseChange_injective_iff (f : M →ₗ[R] N) :
    Injective (f.baseChange A) ↔ Injective (LocalizedModule.map T f) := by
  rw [← LinearMap.coe_restrictScalars R, restrictScalars_baseChange_eq_map T A f,
    IsLocalizedModule.map_injective_iff_localizedModuleMap_injective]

/-- Base change of `f` along a localization of `R` at `T` is surjective if and only if
`LocalizedModule.map T f` is surjective. -/
theorem baseChange_surjective_iff (f : M →ₗ[R] N) :
    Surjective (f.baseChange A) ↔ Surjective (LocalizedModule.map T f) := by
  rw [← LinearMap.coe_restrictScalars R, restrictScalars_baseChange_eq_map T A f,
    IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective]

/-- Base change of `f` along a localization of `R` at `T` is bijective if and only if
`LocalizedModule.map T f` is bijective. -/
theorem baseChange_bijective_iff (f : M →ₗ[R] N) :
    Bijective (f.baseChange A) ↔ Bijective (LocalizedModule.map T f) := by
  rw [← LinearMap.coe_restrictScalars R, restrictScalars_baseChange_eq_map T A f,
    IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective]

end IsLocalization
