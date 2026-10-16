/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.ExteriorPower.BaseChange
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Pullback
public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Affine
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-!
# Pullback of exterior powers of modules on schemes

For a morphism of schemes `f : X ⟶ Y`, `Scheme.Modules.pullbackExteriorPowerComparison f n` is the
canonical natural map `f^* (⋀ⁿ M) ⟶ ⋀ⁿ (f^* M)`, the scheme case of
`TauCeti.SheafOfModules.pullbackExteriorPowerComparison`. It is characterized by its transpose
under the pullback--pushforward adjunction, and it is an isomorphism in degree one.

For a ring map `φ : R ⟶ S`, pullback along `Spec φ` commutes with exterior powers of the
sheaf associated with any `R`-module. The comparison is natural in the module and does not
require flatness, finite presentation, or local freeness. It combines the affine computation
of exterior powers with the identification of pullback with extension of scalars.

This is the affine calculation used to descend exterior-power pullback comparisons on schemes.
It includes finite projective modules and therefore the affine charts of finite locally free
sheaves. The forward component is characterized as the composite of the existing affine
comparisons and the scalar-extension map, whose value on a decomposable wedge is explicit in
`TauCeti.extendScalarsExteriorPowerIso_hom_tmul_mk`.

## References

* The Stacks Project, Lemma 10.13.6 (Tag 0C6F).
* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 (e).
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- Pullback along a morphism of affine spectra commutes with exterior powers of associated
sheaves, naturally in the module, for any ring map. -/
def tildePullbackExteriorPowerIso (n : ℕ) :
    tilde.functor R ⋙ SheafOfModules.exteriorPower (Spec R).sheaf n ⋙
        Scheme.Modules.pullback (Spec.map φ) ≅
      tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ⋙
        SheafOfModules.exteriorPower (Spec S).sheaf n :=
  Functor.isoWhiskerRight (tildeExteriorPowerNatIso (R := R) n).symm
      (Scheme.Modules.pullback (Spec.map φ)) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.exteriorPower.functor R n)
      (tildeFunctorCompPullbackIso φ) ≪≫
    Functor.isoWhiskerRight (TauCeti.extendScalarsExteriorPowerNatIso.{u, u, u} φ.hom n)
      (tilde.functor S) ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars φ.hom)
      (tildeExteriorPowerNatIso (R := S) n) ≪≫
    Functor.isoWhiskerRight (tildeFunctorCompPullbackIso φ).symm
      (SheafOfModules.exteriorPower (Spec S).sheaf n)

/-- The affine pullback comparison is the scalar-extension comparison transported through
`tildeExteriorPowerIso` and `tildeFunctorCompPullbackIso`. -/
@[simp]
theorem tildePullbackExteriorPowerIso_hom_app (n : ℕ) (M : ModuleCat.{u} R) :
    (tildePullbackExteriorPowerIso φ n).hom.app M =
      (Scheme.Modules.pullback (Spec.map φ)).map (tildeExteriorPowerIso n M).inv ≫
        (tildeFunctorCompPullbackIso φ).hom.app (M.exteriorPower n) ≫
        tilde.map (TauCeti.extendScalarsExteriorPowerIso.{u, u, u} φ.hom n M).hom ≫
        (tildeExteriorPowerIso n ((ModuleCat.extendScalars φ.hom).obj M)).hom ≫
        (SheafOfModules.exteriorPower (Spec S).sheaf n).map
          ((tildeFunctorCompPullbackIso φ).inv.app M) := by
  simp only [tildePullbackExteriorPowerIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, tildeExteriorPowerNatIso_inv_app,
    TauCeti.extendScalarsExteriorPowerNatIso_hom_app]
  -- The last two whiskered comparisons have endpoints identified through composite
  -- functors; `erw` crosses those functor-object wrappers before computing components.
  erw [Iso.trans_hom, NatTrans.comp_app]
  simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    tildeExteriorPowerNatIso_hom_app]
  erw [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom]
  rfl

/-- The inverse affine pullback comparison reverses the affine and scalar-extension
comparisons. -/
@[simp]
theorem tildePullbackExteriorPowerIso_inv_app (n : ℕ) (M : ModuleCat.{u} R) :
    (tildePullbackExteriorPowerIso φ n).inv.app M =
      (SheafOfModules.exteriorPower (Spec S).sheaf n).map
          ((tildeFunctorCompPullbackIso φ).hom.app M) ≫
        (tildeExteriorPowerIso n ((ModuleCat.extendScalars φ.hom).obj M)).inv ≫
        tilde.map (TauCeti.extendScalarsExteriorPowerIso.{u, u, u} φ.hom n M).inv ≫
        (tildeFunctorCompPullbackIso φ).inv.app (M.exteriorPower n) ≫
        (Scheme.Modules.pullback (Spec.map φ)).map (tildeExteriorPowerIso n M).hom := by
  simp only [tildePullbackExteriorPowerIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_inv, tildeExteriorPowerNatIso_hom_app,
    TauCeti.extendScalarsExteriorPowerNatIso_inv_app]
  -- As in the forward formula, expose components across the composite-functor wrappers.
  erw [Iso.trans_inv, NatTrans.comp_app]
  simp only [Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    tildeExteriorPowerNatIso_inv_app]
  erw [Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Iso.symm_inv]
  erw [Category.assoc]

end

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical comparison `f^* (⋀ⁿ M) ⟶ ⋀ⁿ (f^* M)` for modules on schemes:
`TauCeti.SheafOfModules.pullbackExteriorPowerComparison` along `f.toRingCatSheafHom`. -/
def pullbackExteriorPowerComparison (n : ℕ) :
    SheafOfModules.exteriorPower Y.sheaf n ⋙ pullback f ⟶
      pullback f ⋙ SheafOfModules.exteriorPower X.sheaf n :=
  TauCeti.SheafOfModules.pullbackExteriorPowerComparison
    (pullbackPushforwardAdjunction f) n

/-- The adjunction equation characterizing the pullback comparison for modules on schemes: its
transpose is the exterior power of the unit `M ⟶ f_* f^* M` followed by the exterior-power
comparison of pushforward. -/
theorem unit_comp_pushforward_map_pullbackExteriorPowerComparison_app (n : ℕ) (M : Y.Modules) :
    (pullbackPushforwardAdjunction f).unit.app ((SheafOfModules.exteriorPower Y.sheaf n).obj M) ≫
        (pushforward f).map ((pullbackExteriorPowerComparison f n).app M) =
      (SheafOfModules.exteriorPower Y.sheaf n).map ((pullbackPushforwardAdjunction f).unit.app M) ≫
        (TauCeti.SheafOfModules.pushforwardExteriorPowerComparison f.toRingCatSheafHom n).app
          ((pullback f).obj M) :=
  TauCeti.SheafOfModules.unit_comp_pushforward_pullbackExteriorPowerComparison
    (pullbackPushforwardAdjunction f) n M

/-- In degree one, the pullback comparison for modules on schemes is the identity of `f^* M`,
read through the identifications `⋀¹ M ≅ M`. -/
theorem pullbackExteriorPowerComparison_app_comp_exteriorPowerOneIso (M : Y.Modules) :
    (pullbackExteriorPowerComparison f 1).app M ≫
        (SheafOfModules.exteriorPowerOneIso X.sheaf).hom.app ((pullback f).obj M) =
      (pullback f).map ((SheafOfModules.exteriorPowerOneIso Y.sheaf).hom.app M) :=
  TauCeti.SheafOfModules.pullbackExteriorPowerComparison_app_comp_exteriorPowerOneIso
    (pullbackPushforwardAdjunction f) M

/-- The pullback comparison for modules on schemes is an isomorphism in degree one. -/
instance isIso_pullbackExteriorPowerComparison_one :
    IsIso (pullbackExteriorPowerComparison f 1) :=
  TauCeti.SheafOfModules.isIso_pullbackExteriorPowerComparison_one (pullbackPushforwardAdjunction f)

end

end AlgebraicGeometry.Scheme.Modules
