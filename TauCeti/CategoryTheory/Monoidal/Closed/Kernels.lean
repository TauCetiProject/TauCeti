/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Internal Hom and cokernel presentations

In a braided closed category with a zero object, internal Hom in its first variable takes a
cokernel presentation to a kernel. In particular, a finite free presentation of a module
sheaf expresses its internal Hom as a kernel between internal Homs from finite free sheaves.

The construction uses Mathlib's preservation of limits by
`MonoidalClosed.internalHom.flip.obj` and the opposite of a cokernel cofork.
-/

public section

open CategoryTheory Limits MonoidalClosed Opposite

namespace TauCeti

noncomputable section

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  {A B M : C} (f : A ⟶ B) (g : B ⟶ M) (w : f ≫ g = 0)
  (h : IsColimit (CokernelCofork.ofπ g w)) (N : C)

/-- Internal Hom turns a cokernel presentation into a kernel presentation, by precomposition.
No projectivity or finiteness condition is needed. -/
def ihomIsKernelOfIsCokernel :
    IsLimit (KernelFork.ofι ((pre g).app N)
      (f := (pre f).app N) (by
        let F := internalHom.flip.obj N
        exact (F.map_comp g.op f.op).symm.trans
          ((congrArg F.map (by simpa using congrArg Quiver.Hom.op w)).trans
            (F.map_zero _ _)))) := by
  let F := internalHom.flip.obj N
  exact KernelFork.mapIsLimit _ (CokernelCofork.IsColimit.ofπOp g w h) F

/-- The internal Hom from the cokernel term of a presentation is canonically the kernel of
precomposition with its relation map. -/
def ihomIsoKernelOfIsCokernel [HasKernel ((pre f).app N)] :
    (ihom M).obj N ≅ kernel ((pre f).app N) :=
  (ihomIsKernelOfIsCokernel f g w h N).conePointUniqueUpToIso (limit.isLimit _)

/-- The kernel inclusion is precomposition with the presentation's quotient map. -/
@[reassoc (attr := simp)]
theorem ihomIsoKernelOfIsCokernel_hom_ι [HasKernel ((pre f).app N)] :
    (ihomIsoKernelOfIsCokernel f g w h N).hom ≫ kernel.ι ((pre f).app N) =
      (pre g).app N :=
  (ihomIsKernelOfIsCokernel f g w h N).conePointUniqueUpToIso_hom_comp
    (limit.isLimit _) WalkingParallelPair.zero

end

end TauCeti
