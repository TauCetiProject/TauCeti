/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.LocallyBijective
public import TauCeti.AlgebraicGeometry.Modules.TensorProduct
public import TauCeti.RingTheory.TensorProduct.IsBaseChange

/-!
# Sections of tensor products over affine opens

For quasi-coherent `𝒪_X`-modules `M` and `N` on a scheme `X` and an affine open `U`, the sections
of the tensor product `M ⊗ N` over `U` are the tensor product of the `Γ(X, U)`-modules of sections:

`Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) ≃ Γ(M ⊗ N, U)`.

The map is the tensor map of the lax monoidal sections functor
`AlgebraicGeometry.Scheme.Modules.sectionsFunctor U`, that is, the sheafification unit at `U` of
the sectionwise tensor product `V ↦ Γ(M, V) ⊗[Γ(X, V)] Γ(N, V)`. It is an instance of
`AlgebraicGeometry.IsAffineOpen.bijective_sheafificationAdjunction_unit_app`: tensor products
commute with base change, so the restrictions of the sectionwise tensor product from `U` to its
basic opens are localizations.

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
quasi-coherent modules is localization at the defining function: tensor products commute with
base change along `Γ(X, U) → Γ(X, D(f))`. -/
theorem isLocalizedModule_tensorObj_map_basicOpen (hU : IsAffineOpen U) (f : Γ(X, U)) :
    IsLocalizedModule (.powers f)
      (PresheafOfModulesOfCommRing.map (R := X.presheaf) (M.val ⊗ N.val)
        (homOfLE (X.basicOpen_le f)).op).hom := by
  let : IsLocalization (.powers f) Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  have hM := (isLocalizedModule_iff_isBaseChange (.powers f) Γ(X, X.basicOpen f) _).mp
    (isLocalizedModule_basicOpenRestrict M hU f)
  have hN := (isLocalizedModule_iff_isBaseChange (.powers f) Γ(X, X.basicOpen f) _).mp
    (isLocalizedModule_basicOpenRestrict N hU f)
  have h := (isLocalizedModule_iff_isBaseChange (.powers f) Γ(X, X.basicOpen f) _).mpr
    (hM.tensorProduct hN)
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
  exact key ▸ IsLocalizedModule.of_linearEquiv (.powers f) _ e (hf := h)

/-- **Sections of tensor products over affine opens.** For quasi-coherent `M` and `N` and an
affine open `U`, the sheafification unit `Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) → Γ(M ⊗ N, U)` of the
sectionwise tensor product is bijective. -/
theorem bijective_tensorObj_unit_app (hU : IsAffineOpen U) :
    Function.Bijective
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (M.val ⊗ N.val)).app (op U)) := by
  have : ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (M.val ⊗ N.val)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (SheafOfModules.tensorUnderlyingIso (R := X.sheaf) M N)
      (inferInstance : (M ⊗ N).IsQuasicoherent)
  exact hU.bijective_sheafificationAdjunction_unit_app
    (isLocalizedModule_tensorObj_map_basicOpen M N hU)

/-- **Sections of tensor products over affine opens.** For quasi-coherent `M` and `N` and an
affine open `U`, the tensor map `Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) → Γ(M ⊗ N, U)` of the sections
functor is bijective. -/
theorem bijective_μ_sectionsFunctor (hU : IsAffineOpen U) :
    Function.Bijective (Functor.LaxMonoidal.μ (sectionsFunctor U) M N) := by
  let F : X.Modules ⥤ PresheafOfModulesOfCommRing.{u} X.presheaf :=
    _root_.SheafOfModules.forget _
  let _ : F.LaxMonoidal := TauCeti.SheafOfModules.forgetLaxMonoidal X.sheaf
  -- The sections functor is `F` followed by evaluation at `U`, whose tensor map is the identity.
  change Function.Bijective ((Functor.LaxMonoidal.μ F M N).app (op U))
  -- `forget_μ` is stated for sheaves of modules over `ringCatSheaf X.sheaf`, which `rw` does not
  -- match against `X.Modules`, so it is first instantiated at the goal's `μ`.
  rw [show Functor.LaxMonoidal.μ F M N = _ from TauCeti.SheafOfModules.forget_μ (R := X.sheaf) M N,
    PresheafOfModules.comp_app]
  -- `forget_μ` is stated with `sheafificationForgetAdjunction`, whose unit agrees with that of
  -- Mathlib's sheafification adjunction up to the comparison `leftAdjointUniq`.
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
