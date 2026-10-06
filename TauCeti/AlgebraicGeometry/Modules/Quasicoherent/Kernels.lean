/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Restriction
public import TauCeti.AlgebraicGeometry.Modules.Restriction
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Kernels of quasicoherent sheaves

The kernel, in the category of all sheaves of modules on a scheme, of a morphism between
quasicoherent sheaves is quasicoherent. No finiteness, separation, or Noetherian hypothesis is
needed. Consequently the full subcategory of quasicoherent sheaves has kernels, and its
inclusion creates them. This allows kernel presentations of sheaf internal Hom to be used
inside quasicoherent sheaves. Restriction to an open subscheme preserves the resulting kernels;
its comparison is Mathlib's `CategoryTheory.Limits.PreservesKernel.iso`.

The affine calculation uses the exactness of `AlgebraicGeometry.tilde.functor` and Mathlib's
`tilde.adjunction`. Restriction to affine opens then gives the result on arbitrary schemes.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.7.
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

private theorem isQuasicoherent_kernel_spec {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (kernel f).IsQuasicoherent := by
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (tildeKernelIso f) inferInstance

private theorem isQuasicoherent_kernel_affine {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} (f : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (kernel f).IsQuasicoherent := by
  let F := Scheme.Modules.restrictFunctor X.isoSpec.inv
  let G := Scheme.Modules.restrictFunctor X.isoSpec.hom
  have : (F.obj (kernel f)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (PreservesKernel.iso F f).symm (isQuasicoherent_kernel_spec (F.map f))
  have : (G.obj (F.obj (kernel f))).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor X.isoSpec.hom _
  let e : G.obj (F.obj (kernel f)) ≅ kernel f :=
    (Scheme.Modules.restrictFunctorComp X.isoSpec.hom X.isoSpec.inv).symm.app _ ≪≫
      (Scheme.Modules.restrictFunctorCongr X.isoSpec.hom_inv_id).app _ ≪≫
      Scheme.Modules.restrictFunctorId.app _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e inferInstance

/-- The ambient kernel of a morphism of quasicoherent sheaves on any scheme is quasicoherent. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel
    {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (kernel f).IsQuasicoherent := by
  refine isQuasicoherent_of_isQuasicoherent_restrict_affineOpens (kernel f) fun U ↦ ?_
  let F := Scheme.Modules.restrictFunctor U.1.ι
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    (PreservesKernel.iso F f).symm (isQuasicoherent_kernel_affine (F.map f))

/-- Quasicoherence is closed under ambient kernels. The generic full-subcategory construction
therefore supplies kernels in `QuasicoherentSheaf X`. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_isClosedUnderKernels
    (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    have := hM
    have := hN
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (limit.isoLimitCone ⟨k, hk⟩) (Scheme.Modules.isQuasicoherent_kernel f)

namespace QuasicoherentSheaf

/-- The inclusion of quasicoherent sheaves preserves kernels: their universal property is the
one in the ambient category of all module sheaves. -/
instance inclusion_preservesKernel {X : Scheme.{u}} {E F : QuasicoherentSheaf X}
    (f : E ⟶ F) :
    PreservesLimit (parallelPair f 0) (ObjectProperty.ι
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)) :=
  ObjectProperty.preservesKernels_ι _ f

end QuasicoherentSheaf

end

end TauCeti.AlgebraicGeometry
