/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Transfer

/-!
# Quasi-coherent modules on an affine scheme

The category of quasi-coherent modules on an affine scheme `X` is abelian and has enough
injectives. Pullback along `X.isoSpec` and Mathlib's tilde equivalence identify it with
`ModuleCat Γ(X, ⊤)`. These are the category theoretic inputs for deriving exact global sections.

Under the tilde equivalence, pullback along `Spec φ` for a ring map `φ : R ⟶ S` is extension of
scalars along `φ` (`tildeEquivFunctorCompPullbackIso`).
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace QuasicoherentSheaf

/-- Quasi-coherent modules on an affine scheme are equivalent to modules over its global
sections. -/
noncomputable def affineEquiv (X : Scheme.{u}) [IsAffine X] :
    QuasicoherentSheaf X ≌ ModuleCat Γ(X, ⊤) :=
  (equivOfIso X.isoSpec).symm.trans (tildeEquiv (R := Γ(X, ⊤))).symm

/-- The forward functor of the affine equivalence is pullback to the spectrum followed by
global sections. -/
@[simp]
theorem affineEquiv_functor (X : Scheme.{u}) [IsAffine X] :
    (affineEquiv X).functor =
      pullback X.isoSpec.inv ⋙ (tildeEquiv (R := Γ(X, ⊤))).inverse := by
  simp [affineEquiv]

/-- The inverse functor of the affine equivalence is tilde followed by pullback to the
affine scheme. -/
@[simp]
theorem affineEquiv_inverse (X : Scheme.{u}) [IsAffine X] :
    (affineEquiv X).inverse =
      (tildeEquiv (R := Γ(X, ⊤))).functor ⋙ pullback X.isoSpec.hom := by
  simp [affineEquiv]

/-- Quasi-coherent modules on an affine scheme form an abelian category. -/
noncomputable instance (X : Scheme.{u}) [IsAffine X] : Abelian (QuasicoherentSheaf X) := by
  let e := affineEquiv X
  letI : Limits.HasFiniteProducts (QuasicoherentSheaf X) :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence e.functor⟩
  exact abelianOfEquivalence e.functor

/-- Quasi-coherent modules on an affine scheme admit injective resolutions. -/
noncomputable instance (X : Scheme.{u}) [IsAffine X] :
    EnoughInjectives (QuasicoherentSheaf X) := by
  let : EnoughInjectives (ModuleCat Γ(X, ⊤)) := ModuleCat.enoughInjectives _
  exact EnoughInjectives.of_equivalence (affineEquiv X).functor

section Pullback

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Under Mathlib's equivalence `tildeEquiv` between modules and quasi-coherent modules on the
spectrum, pullback along `Spec φ` is extension of scalars along `φ`: the pullback of `M~` is
`(S ⊗[R] M)~`, naturally in the `R`-module `M`. This is
`TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso` for quasi-coherent modules. -/
noncomputable def tildeEquivFunctorCompPullbackIso :
    (tildeEquiv (R := R)).functor ⋙ pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ (tildeEquiv (R := S)).functor :=
  ((_root_.SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).fullyFaithfulι.whiskeringRight
    _).preimageIso
      (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (tildeEquiv (R := R)).functor (pullbackCompιIso (Spec.map φ)) ≪≫
        TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso φ)

/-- The underlying morphism of `tildeEquivFunctorCompPullbackIso` is
`TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso`. -/
@[simp]
theorem tildeEquivFunctorCompPullbackIso_hom_app_hom (M : ModuleCat.{u} R) :
    ((tildeEquivFunctorCompPullbackIso φ).hom.app M).hom =
      eqToHom (pullback_obj_obj (Spec.map φ) ((tildeEquiv (R := R)).functor.obj M)) ≫
        (TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso φ).hom.app M := by
  have h := NatTrans.congr_app (Functor.FullyFaithful.map_preimage
    ((_root_.SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).fullyFaithfulι.whiskeringRight
      (ModuleCat.{u} R)) (X := (tildeEquiv (R := R)).functor ⋙ pullback (Spec.map φ))
    (Y := ModuleCat.extendScalars φ.hom ⋙ (tildeEquiv (R := S)).functor)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (tildeEquiv (R := R)).functor (pullbackCompιIso (Spec.map φ)) ≪≫
      TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso φ).hom) M
  refine h.trans ?_
  -- The associator is an identity, and the composite mixes the categories `SheafOfModules` and
  -- `Scheme.Modules`, so neither `simp` nor `rw` applies; the first factor is the identity and
  -- the second is `pullbackCompιIso` by definition of the composite natural transformation.
  exact (Category.id_comp _).trans (congrArg (· ≫ _)
    (pullbackCompιIso_hom_app (Spec.map φ) ((tildeEquiv (R := R)).functor.obj M)))

@[simp]
theorem tildeEquivFunctorCompPullbackIso_inv_app_hom (M : ModuleCat.{u} R) :
    ((tildeEquivFunctorCompPullbackIso φ).inv.app M).hom =
      (TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso φ).inv.app M ≫
        eqToHom (pullback_obj_obj (Spec.map φ) ((tildeEquiv (R := R)).functor.obj M)).symm := by
  have h := NatTrans.congr_app (Functor.FullyFaithful.map_preimage
    ((_root_.SheafOfModules.isQuasicoherent (Spec S).ringCatSheaf).fullyFaithfulι.whiskeringRight
      (ModuleCat.{u} R)) (X := ModuleCat.extendScalars φ.hom ⋙ (tildeEquiv (R := S)).functor)
    (Y := (tildeEquiv (R := R)).functor ⋙ pullback (Spec.map φ))
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (tildeEquiv (R := R)).functor (pullbackCompιIso (Spec.map φ)) ≪≫
      TauCeti.AlgebraicGeometry.tildeFunctorCompPullbackIso φ).inv) M
  refine h.trans ?_
  exact (congrArg (_ ≫ ·) ((Category.comp_id _).trans
    (pullbackCompιIso_inv_app (Spec.map φ) ((tildeEquiv (R := R)).functor.obj M))))

end Pullback

end QuasicoherentSheaf

end AlgebraicGeometry

end TauCeti
