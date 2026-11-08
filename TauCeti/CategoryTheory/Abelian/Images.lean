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

/-- The kernel of the projection of a morphism onto its abelian image is isomorphic to the kernel
of the morphism, whenever the required kernels and cokernel exist. This is the abelian-image
analogue of `CategoryTheory.Limits.kernelFactorThruImage`. -/
noncomputable def kernelFactorThruImage :
    kernel (CategoryTheory.Abelian.factorThruImage f) ≅ kernel f :=
  (kernelCompMono _ (CategoryTheory.Abelian.image.ι f)).symm ≪≫
    kernelIsoOfEq (CategoryTheory.Abelian.image.fac f)

/-- The isomorphism with the kernel of the image projection preserves the kernel inclusion. -/
@[reassoc (attr := simp)]
theorem kernelFactorThruImage_hom_comp_ι :
    (kernelFactorThruImage f).hom ≫ kernel.ι f
      = kernel.ι (CategoryTheory.Abelian.factorThruImage f) := by
  simp [kernelFactorThruImage]

/-- The inverse isomorphism with the kernel of the image projection preserves the inclusion. -/
@[reassoc (attr := simp)]
theorem kernelFactorThruImage_inv_comp_ι :
    (kernelFactorThruImage f).inv ≫ kernel.ι (CategoryTheory.Abelian.factorThruImage f)
      = kernel.ι f := by
  simp [kernelFactorThruImage]

end TauCeti.Abelian
