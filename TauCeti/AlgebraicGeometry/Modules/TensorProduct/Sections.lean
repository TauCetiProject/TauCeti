/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.LocallyBijective
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct

/-!
# Sections of tensor products over affine opens

For quasi-coherent `𝒪_X`-modules `M` and `N` on a scheme `X` and an affine open `U`, the sections
of the tensor product `M ⊗ N` over `U` are the tensor product of the `Γ(X, U)`-modules of sections:

`Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) ≃ Γ(M ⊗ N, U)`.

The map is the tensor map of the lax monoidal sections functor
`AlgebraicGeometry.Scheme.Modules.sectionsFunctor U`, that is, the sheafification unit at `U` of
the sectionwise tensor product `V ↦ Γ(M, V) ⊗[Γ(X, V)] Γ(N, V)`. It is an instance of
`AlgebraicGeometry.IsAffineOpen.bijective_app_of_isLocalizedModule`: localization commutes with
tensor products, so the restrictions of the sectionwise tensor product from `U` to its basic opens
are localizations.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isLocalizedModule_tensorObj_map_basicOpen`: on the basic
  opens of an affine open, the restriction of the sectionwise tensor product is localization;
* `AlgebraicGeometry.Scheme.Modules.bijective_tensorObj_unit_app`: the sheafification unit
  `Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) → Γ(sheafification (M ⊗ N), U)` is bijective;
* `AlgebraicGeometry.Scheme.Modules.bijective_μ_sectionsFunctor`: the tensor map
  `Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) → Γ(M ⊗ N, U)` of the sections functor is bijective.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2.
-/

public section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M N : X.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent] {U : X.Opens}

/-- On the basic opens of an affine open, the restriction in the sectionwise tensor product of two
quasi-coherent modules is localization at the defining function, since localization commutes with
tensor products. -/
theorem isLocalizedModule_tensorObj_map_basicOpen (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsLocalizedModule (.powers f)
      (PresheafOfModulesOfCommRing.map (R := X.presheaf) (M.val ⊗ N.val)
        (homOfLE (X.basicOpen_le f)).op).hom := by
  let : IsLocalization (.powers f) Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  have : IsLocalizedModule (.powers f) (M.basicOpenRestrict f) :=
    isLocalizedModule_basicOpenRestrict M hU f
  have : IsLocalizedModule (.powers f) (N.basicOpenRestrict f) :=
    isLocalizedModule_basicOpenRestrict N hU f
  -- Over `Γ(X, X.basicOpen f)` and over `Γ(X, U)` the tensor products of the restricted sections
  -- agree, because `Γ(X, X.basicOpen f)` is a localization of `Γ(X, U)`.
  have := IsLocalization.tensorProduct_compatibleSMul (.powers f) Γ(X, X.basicOpen f)
    Γ(M, X.basicOpen f) Γ(N, X.basicOpen f)
  -- The sectionwise tensor product over `X.basicOpen f` is a `Γ(X, U)`-module by restriction of
  -- scalars, which agrees with the module structure through the left factor.
  let e : TensorProduct Γ(X, X.basicOpen f) Γ(M, X.basicOpen f) Γ(N, X.basicOpen f) ≃ₗ[Γ(X, U)]
      (ModuleCat.restrictScalars (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom).obj
        (PresheafOfModulesOfCommRing.obj (R := X.presheaf) (M.val ⊗ N.val)
          (op (X.basicOpen f))) :=
    { toFun x := x
      invFun x := x
      map_add' _ _ := rfl
      map_smul' r x := by
        induction x using TensorProduct.inductionOn with
        | tmul => rfl
        | add x y hx hy =>
          rw [smul_add]
          exact (congrArg₂ (· + ·) hx hy).trans (smul_add _ _ _).symm
      left_inv _ := rfl
      right_inv _ := rfl }
  have key : e.toLinearMap ∘ₗ TensorProduct.mapOfCompatibleSMul Γ(X, X.basicOpen f) Γ(X, U)
      Γ(X, U) Γ(M, X.basicOpen f) Γ(N, X.basicOpen f) ∘ₗ
        TensorProduct.map (M.basicOpenRestrict f) (N.basicOpenRestrict f) =
      (PresheafOfModulesOfCommRing.map (R := X.presheaf) (M.val ⊗ N.val)
        (homOfLE (X.basicOpen_le f)).op).hom :=
    TensorProduct.ext' fun _ _ ↦ by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.map_tmul,
        TensorProduct.mapOfCompatibleSMul_tmul]
      -- The restriction of the sectionwise tensor product is applied through `ModuleCat.Hom.hom`
      -- of `PresheafOfModulesOfCommRing.map`, which `tensorObj_map_tmul` states with
      -- `DFunLike.coe` at the restriction of scalars; `erw` sees through the two wrappers.
      erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
      exact congrArg₂ (· ⊗ₜ ·) (M.basicOpenRestrict_apply f _) (N.basicOpenRestrict_apply f _)
  -- The linear map underlying `equivOfCompatibleSMul` is by definition `mapOfCompatibleSMul`, and
  -- that of a composite of linear equivalences is the composite of the linear maps.
  have h : IsLocalizedModule (.powers f) (e.toLinearMap ∘ₗ TensorProduct.mapOfCompatibleSMul
      Γ(X, X.basicOpen f) Γ(X, U) Γ(X, U) Γ(M, X.basicOpen f) Γ(N, X.basicOpen f) ∘ₗ
        TensorProduct.map (M.basicOpenRestrict f) (N.basicOpenRestrict f)) :=
    IsLocalizedModule.of_linearEquiv (.powers f) _
      (TensorProduct.equivOfCompatibleSMul Γ(X, X.basicOpen f) Γ(X, U) Γ(X, U) _ _ ≪≫ₗ e)
  exact key ▸ h

/-- For quasi-coherent `M` and `N` and an affine open `U`, the sheafification unit
`Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) → Γ(sheafification (M ⊗ N), U)` of the sectionwise tensor product
`V ↦ Γ(M, V) ⊗[Γ(X, V)] Γ(N, V)` is bijective. Its codomain is identified with `Γ(M ⊗ N, U)` by
`SheafOfModules.tensorUnderlyingIso`, which gives `bijective_μ_sectionsFunctor`. -/
theorem bijective_tensorObj_unit_app (hU : IsAffineOpen U) :
    Function.Bijective
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (M.val ⊗ N.val)).app (op U)) := by
  have : ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (M.val ⊗ N.val)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (SheafOfModules.tensorUnderlyingIso (R := X.sheaf) M N)
      (inferInstanceAs (M ⊗ N).IsQuasicoherent)
  exact hU.bijective_sheafification_unit_app_of_isLocalizedModule fun f ↦
    isLocalizedModule_tensorObj_map_basicOpen M N hU f

/-- **Sections of tensor products over affine opens.** For quasi-coherent `M` and `N` and an
affine open `U`, the tensor map `Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) → Γ(M ⊗ N, U)` of the sections
functor is bijective. -/
theorem bijective_μ_sectionsFunctor (hU : IsAffineOpen U) :
    Function.Bijective (Functor.LaxMonoidal.μ (sectionsFunctor U) M N) := by
  rw [sectionsFunctor_μ, PresheafOfModules.comp_app]
  -- `sectionsFunctor_μ` is stated with `sheafificationForgetAdjunction`, whose unit agrees with
  -- that of Mathlib's sheafification adjunction up to the comparison `leftAdjointUniq`.
  have h := congrArg (fun φ ↦ φ.app (op U)) (Adjunction.unit_leftAdjointUniq_hom_app
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj))
    (TauCeti.SheafOfModules.sheafificationForgetAdjunction X.sheaf) (M.val ⊗ N.val))
  have hu : Function.Bijective (((TauCeti.SheafOfModules.sheafificationForgetAdjunction
      X.sheaf).unit.app (M.val ⊗ N.val)).app (op U)) := by
    rw [← h]
    exact ((TauCeti.PresheafOfModulesOfCommRing.evaluation (op U)).mapIso
      ((SheafOfModules.forget _).mapIso ((Adjunction.leftAdjointUniq
        (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj))
        (TauCeti.SheafOfModules.sheafificationForgetAdjunction X.sheaf)).app
          (M.val ⊗ N.val)))).toLinearEquiv.bijective.comp (bijective_tensorObj_unit_app M N hU)
  exact ((TauCeti.PresheafOfModulesOfCommRing.evaluation (op U)).mapIso
    ((SheafOfModules.forget _).mapIso
      (SheafOfModules.tensorUnderlyingIso (R := X.sheaf) M N).symm)).toLinearEquiv.bijective.comp hu

end AlgebraicGeometry.Scheme.Modules
