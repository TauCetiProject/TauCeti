/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape

/-!
# Zero objects are closed under colimits

In a category with zero morphisms, a colimit of zero objects is a zero object: the zero objects
are closed under colimits of every shape. Combined with the closure of kernels and cokernels under
colimits of morphisms (`CategoryTheory.ObjectProperty.prop_kernel_colimMap`), this says that a
colimit of isomorphisms is an isomorphism when colimits are exact.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

/-- A colimit of zero objects is a zero object. -/
instance {C : Type*} [Category* C] [HasZeroMorphisms C] {J : Type*} [Category* J] :
    IsClosedUnderColimitsOfShape (IsZero (C := C)) J where
  colimitsOfShape_le := by
    rintro X ⟨h⟩
    rw [IsZero.iff_id_eq_zero]
    exact h.isColimit.hom_ext fun j ↦ (h.prop_diag_obj j).eq_of_src _ _

end CategoryTheory.ObjectProperty
