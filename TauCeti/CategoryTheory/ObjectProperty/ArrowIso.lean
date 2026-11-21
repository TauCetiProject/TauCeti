/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Kernels and cokernels of isomorphic arrows

Let `S` be a property of objects closed under isomorphisms. If two arrows `f` and `f'` are
isomorphic, then the kernel of `f` satisfies `S` exactly when the kernel of `f'` does, and likewise
for the cokernels (`CategoryTheory.ObjectProperty.prop_kernel_of_arrowIso`,
`CategoryTheory.ObjectProperty.prop_cokernel_of_arrowIso`): the isomorphism of arrows induces
isomorphisms `kernel f ≅ kernel f'` and `cokernel f ≅ cokernel f'` (`kernel.mapIso`,
`cokernel.mapIso`).
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ObjectProperty C)
  [S.IsClosedUnderIsomorphisms] {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- The kernel of a morphism satisfies a property closed under isomorphisms as soon as the kernel
of an isomorphic arrow does. -/
lemma prop_kernel_of_arrowIso [HasKernel f] [HasKernel f'] (e : Arrow.mk f ≅ Arrow.mk f')
    (h : S (kernel f)) : S (kernel f') :=
  S.prop_of_iso (kernel.mapIso f f' (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e)
    (Arrow.w e.hom).symm) h

/-- The cokernel of a morphism satisfies a property closed under isomorphisms as soon as the
cokernel of an isomorphic arrow does. -/
lemma prop_cokernel_of_arrowIso [HasCokernel f] [HasCokernel f'] (e : Arrow.mk f ≅ Arrow.mk f')
    (h : S (cokernel f)) : S (cokernel f') :=
  S.prop_of_iso (cokernel.mapIso f f' (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e)
    (Arrow.w e.hom).symm) h

end CategoryTheory.ObjectProperty
