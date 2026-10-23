/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.Images

/-!
# Kernels of projections onto abelian images

The projection of a morphism onto its abelian image has the same kernel as the morphism.
This identifies the first term of the kernel-image sequence without requiring the category
to be abelian. The construction complements `CategoryTheory.Limits.kernelFactorThruImage`,
which uses the categorical image rather than the kernel of the cokernel.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace TauCeti.Abelian

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y)
  [HasCokernel f] [HasKernel (cokernel.π f)] [HasKernel f]
  [HasKernel (CategoryTheory.Abelian.factorThruImage f)]

/-- The kernel of a morphism is isomorphic to the kernel of its projection onto the abelian
image, whenever the required kernels and cokernel exist. -/
noncomputable def kernelFactorThruImageIso :
    kernel f ≅ kernel (CategoryTheory.Abelian.factorThruImage f) :=
  kernelIsoOfEq (CategoryTheory.Abelian.image.fac f).symm ≪≫ kernelCompMono _ _

/-- The isomorphism with the kernel of the image projection preserves the kernel inclusion. -/
@[reassoc (attr := simp)]
theorem kernelFactorThruImageIso_hom_comp_ι :
    (kernelFactorThruImageIso f).hom ≫ kernel.ι (CategoryTheory.Abelian.factorThruImage f)
      = kernel.ι f := by
  simp [kernelFactorThruImageIso]

/-- The inverse isomorphism with the kernel of the image projection preserves the inclusion. -/
@[reassoc (attr := simp)]
theorem kernelFactorThruImageIso_inv_comp_ι :
    (kernelFactorThruImageIso f).inv ≫ kernel.ι f
      = kernel.ι (CategoryTheory.Abelian.factorThruImage f) := by
  simp [kernelFactorThruImageIso]

end TauCeti.Abelian
