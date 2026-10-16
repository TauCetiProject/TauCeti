/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Cokernels of quasicoherent sheaves

The cokernel in the category of all sheaves of modules of a morphism between quasicoherent
sheaves is quasicoherent. On a spectrum it is the sheaf associated with the cokernel of the
map on global sections. Restriction to affine opens gives the result on arbitrary schemes,
without Noetherian or separation assumptions.

Consequently quasicoherent sheaves have cokernels and their inclusion preserves them.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.7.
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

/-- The ambient cokernel of a morphism of quasicoherent sheaves on a spectrum is the sheaf
associated with the cokernel of its map on global sections. -/
def _root_.AlgebraicGeometry.Scheme.Modules.tildeCokernelIso {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    tilde (cokernel ((moduleSpecΓFunctor (R := R)).map f)) ≅ cokernel f :=
  PreservesCokernel.iso (tilde.functor R) _ ≪≫
    cokernel.mapIso _ _
      (@asIso _ _ _ _ M.fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M))
      (@asIso _ _ _ _ N.fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) N))
      ((tilde.adjunction (R := R)).counit.naturality f)

/-- The affine cokernel comparison intertwines the quotient maps through the counit of the
associated-sheaf/global-sections adjunction. -/
@[reassoc (attr := simp)]
theorem _root_.AlgebraicGeometry.Scheme.Modules.map_π_comp_tildeCokernelIso_hom
    {R : CommRingCat.{u}} {M N : (Spec R).Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    tilde.map (cokernel.π ((moduleSpecΓFunctor (R := R)).map f)) ≫
      (tildeCokernelIso f).hom = N.fromTildeΓ ≫ cokernel.π f := by
  rw [← tilde.functor_map, tildeCokernelIso]
  -- The comparison is in the underlying category of sheaves of modules; `erw` identifies
  -- this with the scheme-module presentation before applying the cokernel formulas.
  erw [Iso.trans_hom, ← Category.assoc, PreservesCokernel.π_iso_hom,
    cokernel.mapIso_hom, cokernel.π_desc]
  rfl

private theorem isQuasicoherent_cokernel_spec {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel f).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (tildeCokernelIso f) inferInstance

private theorem isQuasicoherent_cokernel_affine {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (cokernel f).IsQuasicoherent := by
  let F := Scheme.Modules.restrictFunctor X.isoSpec.inv
  have : (F.obj (cokernel f)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (PreservesCokernel.iso F f).symm (isQuasicoherent_cokernel_spec (F.map f))
  exact isQuasicoherent_of_isQuasicoherent_restrict_iso X.isoSpec (cokernel f)

/-- The ambient cokernel of a morphism of quasicoherent sheaves on any scheme is quasicoherent. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (cokernel f).IsQuasicoherent := by
  refine isQuasicoherent_of_isQuasicoherent_restrict_affineOpens (cokernel f) fun U ↦ ?_
  let F := Scheme.Modules.restrictFunctor U.1.ι
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    (PreservesCokernel.iso F f).symm (isQuasicoherent_cokernel_affine (F.map f))

/-- Quasicoherence is closed under ambient cokernels, so the generic full-subcategory
construction supplies cokernels in `QuasicoherentSheaf X`. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderCokernels
    (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    have := hM
    have := hN
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (colimit.isoColimitCocone ⟨k, hk⟩) (Scheme.Modules.isQuasicoherent_cokernel f)

namespace QuasicoherentSheaf

/-- The inclusion of quasicoherent sheaves preserves cokernels: their universal property is
the one in the ambient category of all module sheaves. -/
instance inclusion_preservesCokernel {X : Scheme.{u}} {E F : QuasicoherentSheaf X}
    (f : E ⟶ F) :
    PreservesColimit (parallelPair f 0) (ObjectProperty.ι
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)) :=
  ObjectProperty.preservesCokernels_ι _ f

end QuasicoherentSheaf

end

end TauCeti.AlgebraicGeometry
