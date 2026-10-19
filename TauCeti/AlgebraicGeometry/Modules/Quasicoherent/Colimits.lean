/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction

/-!
# Colimits of quasicoherent sheaves

The colimit, in the category of all sheaves of modules on a scheme, of a small diagram of
quasicoherent sheaves is quasicoherent. On a spectrum it is the sheaf associated with the colimit
of the modules of global sections, since the associated-sheaf functor `M ↦ M~` is a left adjoint
and a quasicoherent sheaf is the sheaf associated with its global sections. Restriction to an
open subscheme is also a left adjoint, so restriction to affine opens gives the result on
arbitrary schemes, without Noetherian or separation assumptions.

In particular direct sums of quasicoherent sheaves are quasicoherent, such as the direct sum of
the homogeneous components of a graded quasicoherent algebra.

## Main declarations

* `TauCeti.AlgebraicGeometry.isQuasicoherent_of_isColimit`: a small colimit of quasicoherent
  sheaves is quasicoherent;
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderColimitsOfShape`: quasicoherence
  is closed under small colimits;
* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_sigma`: a small coproduct of quasicoherent
  sheaves is quasicoherent.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 (`M ↦ M~` commutes with direct sums)
  and Proposition II.5.7.
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe w w' u

noncomputable section

variable {J : Type w} [Category.{w'} J] [EssentiallySmall.{u} J]

/-- On a spectrum, a small colimit of quasicoherent sheaves is quasicoherent: it is the sheaf
associated with the colimit of their modules of global sections. -/
private theorem isQuasicoherent_of_isColimit_spec {R : CommRingCat.{u}}
    {K : J ⥤ (Spec R).Modules} (hK : ∀ j, (K.obj j).IsQuasicoherent)
    {c : Cocone K} (hc : IsColimit c) : c.pt.IsQuasicoherent := by
  have := hasColimitsOfShape_of_essentiallySmall.{u} J (ModuleCat.{u} R)
  -- Each `K.obj j` is the sheaf associated with its global sections, and `M ↦ M~` preserves
  -- colimits, so `c.pt` is the sheaf associated with the colimit of the global sections.
  have (j : J) :
      IsIso ((Functor.whiskerLeft K (tilde.adjunction (R := R)).counit).app j) :=
    (isQuasicoherent_iff_isIso_fromTildeΓ (K.obj j)).1 (hK j)
  have : IsIso (Functor.whiskerLeft K (tilde.adjunction (R := R)).counit) :=
    NatIso.isIso_of_isIso_app _
  let e : K ⋙ moduleSpecΓFunctor ⋙ tilde.functor R ≅ K :=
    asIso (Functor.whiskerLeft K (tilde.adjunction (R := R)).counit)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (IsColimit.coconePointsIsoOfNatIso (isColimitOfPreserves (tilde.functor R)
      (colimit.isColimit (K ⋙ moduleSpecΓFunctor))) hc e)
    (inferInstanceAs ((tilde.functor R).obj (colimit (K ⋙ moduleSpecΓFunctor))).IsQuasicoherent)

private theorem isQuasicoherent_of_isColimit_affine {X : Scheme.{u}} [IsAffine X]
    {K : J ⥤ X.Modules} (hK : ∀ j, (K.obj j).IsQuasicoherent)
    {c : Cocone K} (hc : IsColimit c) : c.pt.IsQuasicoherent := by
  have : ((restrictFunctor X.isoSpec.inv).obj c.pt).IsQuasicoherent :=
    isQuasicoherent_of_isColimit_spec (K := K ⋙ restrictFunctor X.isoSpec.inv)
      (fun j ↦ have := hK j; isQuasicoherent_restrictFunctor _ _)
      (isColimitOfPreserves (restrictFunctor X.isoSpec.inv) hc)
  exact isQuasicoherent_of_isQuasicoherent_restrict_iso X.isoSpec c.pt

/-- On any scheme, the colimit, in the category of all sheaves of modules, of a small diagram of
quasicoherent sheaves is quasicoherent. -/
theorem isQuasicoherent_of_isColimit {X : Scheme.{u}} {K : J ⥤ X.Modules}
    (hK : ∀ j, (K.obj j).IsQuasicoherent) {c : Cocone K} (hc : IsColimit c) :
    c.pt.IsQuasicoherent := by
  -- Restriction to an open subscheme is a left adjoint, so it preserves the colimit.
  refine isQuasicoherent_of_isQuasicoherent_restrict_affineOpens c.pt fun U ↦ ?_
  exact isQuasicoherent_of_isColimit_affine (K := K ⋙ restrictFunctor U.1.ι)
    (fun j ↦ have := hK j; isQuasicoherent_restrictFunctor _ _)
    (isColimitOfPreserves (restrictFunctor U.1.ι) hc)

variable (J) in
/-- Quasicoherence is closed under small colimits in the category of all sheaves of modules, so
the generic full-subcategory construction supplies these colimits in `QuasicoherentSheaf X`. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderColimitsOfShape
    (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le _ := fun ⟨h⟩ ↦ isQuasicoherent_of_isColimit h.prop_diag_obj h.isColimit

/-- The coproduct of a small family of quasicoherent sheaves on any scheme is quasicoherent. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_sigma {X : Scheme.{u}}
    {ι : Type w} [Small.{u} ι] (M : ι → X.Modules) [HasCoproduct M]
    [∀ i, (M i).IsQuasicoherent] : (∐ M).IsQuasicoherent :=
  isQuasicoherent_of_isColimit (fun i ↦ inferInstanceAs (M i.as).IsQuasicoherent)
    (colimit.isColimit _)

end

end TauCeti.AlgebraicGeometry
