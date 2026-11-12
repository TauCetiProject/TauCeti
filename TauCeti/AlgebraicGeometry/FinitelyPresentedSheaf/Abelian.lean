/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.Basic
public import TauCeti.AlgebraicGeometry.Modules.FinitePresentation.Abelian

/-!
# Coherent sheaves on locally Noetherian schemes

Finitely presented sheaves on a locally Noetherian scheme form an abelian category, and their
inclusion into all sheaves of modules preserves finite limits and finite colimits. Thus coherent
kernels and cokernels can be used directly in the ambient long exact cohomology sequence. In
particular, the kernel of a finite sum of twisting sheaves surjecting onto a coherent sheaf is
again coherent, as needed in the dimension-shifting proof of finiteness of projective cohomology.

The kernel statement only requires a quasi-coherent target and a quasi-coherent source of finite
type. The cokernel statement holds on any scheme, without a Noetherian hypothesis, when the
source is quasi-coherent of finite type and the target is finitely presented. Both follow from
the corresponding affine calculations by restriction to affine opens and descent of finite
presentation. No quasi-compactness or separation assumption is needed. The affine inputs are
`Scheme.Modules.isFinitePresentation_kernel_spec` and
`Scheme.Modules.isFinitePresentation_cokernel_spec`; the abelian structure uses Mathlib's
`CategoryTheory.ObjectProperty` construction for subcategories closed under kernels, cokernels
and finite products.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.7.
* The Stacks Project, Section 30.9 (Tag 01XY), coherent sheaves on locally Noetherian schemes.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf

/-- Coherent sheaves on a locally Noetherian scheme form an abelian category. -/
noncomputable instance (X : Scheme.{u}) [IsLocallyNoetherian X] :
    Abelian (FinitelyPresentedSheaf X) := inferInstanceAs
      (Abelian (ObjectProperty.FullSubcategory
        (SheafOfModules.isFinitePresentation X.ringCatSheaf)))

end TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf
