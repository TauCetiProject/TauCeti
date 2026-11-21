/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty

/-!
# Isomorphisms modulo the Serre class of zero objects

For the Serre class of zero objects of an abelian category, an isomorphism modulo the class is an
isomorphism (`CategoryTheory.ObjectProperty.isoModSerre_isZero_iff`). This recovers statements
about isomorphisms as the zero-object case of their versions modulo a Serre class.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- A morphism is an isomorphism modulo the Serre class of zero objects if and only if it is an
isomorphism. -/
lemma isoModSerre_isZero_iff {X Y : C} (f : X ⟶ Y) :
    isoModSerre IsZero f ↔ IsIso f := by
  refine ⟨fun h ↦ ?_, fun _ ↦ isoModSerre_of_isIso _ f⟩
  have := Preadditive.mono_of_isZero_kernel _ h.1
  have := Preadditive.epi_of_isZero_cokernel _ h.2
  exact isIso_of_mono_of_epi f

end CategoryTheory.ObjectProperty
