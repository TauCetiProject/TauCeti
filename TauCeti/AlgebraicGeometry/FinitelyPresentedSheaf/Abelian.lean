/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.Basic
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation
public import TauCeti.AlgebraicGeometry.Modules.Biprod
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# The abelian category of coherent sheaves

On a locally Noetherian scheme, finitely presented sheaves are coherent and form an abelian
category. Their kernels and cokernels are computed in all sheaves of modules, and the inclusion
preserves finite limits and finite colimits. Consequently, a short exact sequence of coherent
sheaves remains short exact as a sequence of module sheaves, where sheaf cohomology applies.

Cokernel closure needs no Noetherian hypothesis.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.4.
* The Stacks Project, *Properties of Schemes*, Section 28.17 (Tag 01PA).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf

universe u

noncomputable section

variable (X : Scheme.{u})

/-- Finitely presented sheaves admit finite direct sums on any scheme. -/
instance : HasFiniteBiproducts (FinitelyPresentedSheaf X) := by
  have := TauCeti.SheafOfModules.isClosedUnderFiniteProducts_isFinitePresentation
    (R := X.ringCatSheaf)
  exact HasFiniteBiproducts.of_hasFiniteProducts

/-- Cokernels of morphisms of finitely presented sheaves are finitely presented. -/
instance isClosedUnderCokernels :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, c, hc, hM, hN⟩
    let := hM
    let := hN
    exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      ((cokernelIsCokernel f).coconePointUniqueUpToIso hc)
      (Scheme.Modules.isFinitePresentation_cokernel f)

/-- The inclusion of finitely presented sheaves into module sheaves preserves finite colimits. -/
instance preservesFiniteColimits_inclusion :
    PreservesFiniteColimits
      (ObjectProperty.ι (SheafOfModules.isFinitePresentation X.ringCatSheaf)) := by
  have : HasCoequalizers (FinitelyPresentedSheaf X) := Preadditive.hasCoequalizers_of_hasCokernels
  have : HasBinaryBiproducts (FinitelyPresentedSheaf X) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have := (SheafOfModules.isFinitePresentation X.ringCatSheaf).preservesCokernels_ι
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

variable [IsLocallyNoetherian X]

/-- Kernels of morphisms of coherent sheaves are coherent. -/
instance isClosedUnderKernels :
    (SheafOfModules.isFinitePresentation X.ringCatSheaf).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, c, hc, hM, hN⟩
    let := hM
    let := hN
    exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
      ((kernelIsKernel f).conePointUniqueUpToIso hc)
      (Scheme.Modules.isFinitePresentation_kernel f)

/-- Coherent sheaves on a locally Noetherian scheme form an abelian category. -/
instance : Abelian (FinitelyPresentedSheaf X) := by
  have := TauCeti.SheafOfModules.containsZero_isFinitePresentation (R := X.ringCatSheaf)
  have := TauCeti.SheafOfModules.isClosedUnderFiniteProducts_isFinitePresentation
    (R := X.ringCatSheaf)
  infer_instance

/-- The inclusion of coherent sheaves into module sheaves preserves finite limits. -/
instance preservesFiniteLimits_inclusion :
    PreservesFiniteLimits
      (ObjectProperty.ι (SheafOfModules.isFinitePresentation X.ringCatSheaf)) := by
  have := (SheafOfModules.isFinitePresentation X.ringCatSheaf).preservesKernels_ι
  exact Functor.preservesFiniteLimits_of_preservesKernels _

end

end TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf
