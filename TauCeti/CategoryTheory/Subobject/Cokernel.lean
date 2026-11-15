/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Cokernels of inclusions of subobjects

For subobjects `A ≤ B` of an object `X`, the cokernel of the inclusion `Subobject.ofLE A B h` is
the quotient `B / A`. This file records that this quotient only depends on `A` and `B` up to
equality (`CategoryTheory.Subobject.cokernelOfLEIsoOfEq`), which is used to rewrite the indices of
the graded pieces of a filtration.

## Main definitions

* `CategoryTheory.Subobject.cokernelOfLEIsoOfEq`: the canonical isomorphism between the cokernels
  of the inclusions of equal pairs of subobjects.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Subobject

variable {C : Type*} [Category* C] [HasZeroMorphisms C] {X : C}

/-- The cokernel of an inclusion `A ≤ B` of subobjects is unchanged, up to the canonical
isomorphism, when `A` and `B` are replaced by equal subobjects. -/
noncomputable def cokernelOfLEIsoOfEq {A B A' B' : Subobject X} (hA : A = A') (hB : B = B')
    (h : A ≤ B) (h' : A' ≤ B') [HasCokernel (ofLE A B h)] [HasCokernel (ofLE A' B' h')] :
    cokernel (ofLE A B h) ≅ cokernel (ofLE A' B' h') :=
  eqToIso (by subst hA hB; rfl)

end CategoryTheory.Subobject
