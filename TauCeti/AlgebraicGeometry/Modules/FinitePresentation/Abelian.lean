/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Restriction.FinitePresentation
public import TauCeti.AlgebraicGeometry.Modules.Restriction.FiniteType
public import TauCeti.AlgebraicGeometry.Modules.Biprod
public import TauCeti.CategoryTheory.ObjectProperty
public import TauCeti.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.Subcategory

/-!
# Finite presentation and ambient closure properties

On a locally Noetherian scheme, the kernel of a morphism from a quasi-coherent sheaf of finite
type to a quasi-coherent sheaf is finitely presented. No quasi-compactness or separation
assumption is needed.

This follows from `Scheme.Modules.isFinitePresentation_kernel_spec` by restriction to affine
opens and descent of finite presentation. It applies to ambient scheme modules independently
of the bundled category of finitely presented sheaves. The corresponding cokernel result is
provided by `Scheme.Modules.isFinitePresentation_cokernel` in the restriction module.

The finite-presentation object property contains zero and is closed under cokernels and finite
products on every scheme, and under kernels on locally Noetherian schemes. The generic
object-property instances therefore give an abelian full subcategory in the locally Noetherian
case, whose inclusion preserves finite limits and finite colimits.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.7.
* The Stacks Project, Section 30.9 (Tag 01XY), coherent sheaves on locally Noetherian schemes.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- On a locally Noetherian scheme the ambient kernel of a morphism from a quasi-coherent
sheaf of finite type to a quasi-coherent sheaf is finitely presented. -/
instance isFinitePresentation_kernel [IsLocallyNoetherian X] (f : M ⟶ N)
    [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] :
    (kernel f).IsFinitePresentation := by
  refine isFinitePresentation_of_isFinitePresentation_restrict (kernel f)
    (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X) fun U ↦ ?_
  let F := restrictFunctor U.1.ι
  let G := restrictFunctor U.2.isoSpec.inv
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  apply (isFinitePresentation_restrict_iff_of_isIso _ U.2.isoSpec.inv).mp
  exact (SheafOfModules.isFinitePresentation (Spec Γ(X, U.1)).ringCatSheaf).prop_of_iso
    (G.mapIso (PreservesKernel.iso F f) ≪≫ PreservesKernel.iso G (F.map f)).symm
    (isFinitePresentation_kernel_spec (G.map (F.map f)))

/-- Finitely presented sheaves are closed under ambient cokernels on every scheme. -/
instance isFinitePresentation_isClosedUnderCokernels (X : Scheme.{u}) :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, c, hc, hM, hN⟩
    have := hM
    have := hN
    exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      (colimit.isoColimitCocone ⟨c, hc⟩) (isFinitePresentation_cokernel f)

/-- Coherent sheaves on a locally Noetherian scheme are closed under ambient kernels. -/
instance isFinitePresentation_isClosedUnderKernels (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    have := hM
    have := hN
    exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      (limit.isoLimitCone ⟨k, hk⟩) (isFinitePresentation_kernel f)

/-- The zero module sheaf is finitely presented. -/
instance isFinitePresentation_containsZero (X : Scheme.{u}) :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).ContainsZero where
  exists_zero := ⟨_, TauCeti.SheafOfModules.isZero_free PEmpty, inferInstance⟩

/-- Finitely presented sheaves are closed under binary products, computed as direct sums. -/
instance isFinitePresentation_isClosedUnderBinaryProducts (X : Scheme.{u}) :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderBinaryProducts :=
  ObjectProperty.isClosedUnderBinaryProducts_of_prop_biprod _ fun A B hA hB ↦ by
    let := hA
    let := hB
    exact Scheme.Modules.isFinitePresentation_biprod A B

/-- Finitely presented sheaves are closed under finite products. -/
instance isFinitePresentation_isClosedUnderFiniteProducts (X : Scheme.{u}) :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderFiniteProducts := .mk'

end AlgebraicGeometry.Scheme.Modules
