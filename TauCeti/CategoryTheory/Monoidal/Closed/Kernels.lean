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

/-- Precomposition reverses a zero composite into a zero composite of internal Hom maps. -/
@[reassoc (attr := simp)]
theorem pre_app_comp_pre_app_eq_zero (w : f ≫ g = 0) (N : C) :
    (pre g).app N ≫ (pre f).app N = 0 := by
  rw [← NatTrans.comp_app, ← pre_map, w]
  exact (internalHom.flip.obj N).map_zero _ _

/-- Internal Hom turns a cokernel presentation into a kernel presentation, by precomposition.
No projectivity or finiteness condition is needed. -/
def isLimitKernelForkPreOfIsColimit :
    IsLimit (KernelFork.ofι ((pre g).app N)
      (f := (pre f).app N) (pre_app_comp_pre_app_eq_zero f g w N)) := by
  let F := internalHom.flip.obj N
  exact KernelFork.mapIsLimit _ (CokernelCofork.IsColimit.ofπOp g w h) F

/-- The internal Hom from the cokernel term of a presentation is canonically the kernel of
precomposition with its relation map. -/
def ihomIsoKernelOfIsColimit [HasKernel ((pre f).app N)] :
    (ihom M).obj N ≅ kernel ((pre f).app N) :=
  (isLimitKernelForkPreOfIsColimit f g w h N).conePointUniqueUpToIso (limit.isLimit _)

/-- The kernel inclusion is precomposition with the presentation's quotient map. -/
@[reassoc (attr := simp)]
theorem ihomIsoKernelOfIsColimit_hom_ι [HasKernel ((pre f).app N)] :
    (ihomIsoKernelOfIsColimit f g w h N).hom ≫ kernel.ι ((pre f).app N) =
      (pre g).app N :=
  (isLimitKernelForkPreOfIsColimit f g w h N).conePointUniqueUpToIso_hom_comp
    (limit.isLimit _) WalkingParallelPair.zero

end

end TauCeti
