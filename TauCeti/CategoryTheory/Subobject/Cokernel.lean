/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Balanced
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Cokernels of inclusions of subobjects

For subobjects `A ≤ B` of an object `X`, the cokernel of the inclusion `Subobject.ofLE A B h` is
the quotient `B / A`. This file records that this quotient only depends on `A` and `B` up to
equality (`CategoryTheory.Subobject.cokernelOfLEIsoOfEq`), and that it vanishes if and only if
`A = B` (`CategoryTheory.Subobject.isZero_cokernel_ofLE_iff`).

## Main definitions

* `CategoryTheory.Subobject.cokernelOfLEIsoOfEq`: the canonical isomorphism between the cokernels
  of the inclusions of equal pairs of subobjects. It is induced by the inclusion `B ≤ B'`
  (`CategoryTheory.Subobject.π_cokernelOfLEIsoOfEq_hom`).
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Subobject

variable {C : Type*} [Category* C] {X : C}

/-- The cokernel of an inclusion `A ≤ B` of subobjects is unchanged, up to the canonical
isomorphism, when `A` and `B` are replaced by equal subobjects. -/
noncomputable def cokernelOfLEIsoOfEq [HasZeroMorphisms C] {A B A' B' : Subobject X}
    (hA : A = A') (hB : B = B') (h : A ≤ B) (h' : A' ≤ B')
    [HasCokernel (ofLE A B h)] [HasCokernel (ofLE A' B' h')] :
    cokernel (ofLE A B h) ≅ cokernel (ofLE A' B' h') :=
  eqToIso (by subst hA hB; rfl)

/-- The isomorphism `CategoryTheory.Subobject.cokernelOfLEIsoOfEq` is induced by the inclusion of
`B` into the equal subobject `B'`. -/
@[reassoc (attr := simp)]
lemma π_cokernelOfLEIsoOfEq_hom [HasZeroMorphisms C] {A B A' B' : Subobject X} (hA : A = A')
    (hB : B = B') (h : A ≤ B) (h' : A' ≤ B') [HasCokernel (ofLE A B h)]
    [HasCokernel (ofLE A' B' h')] :
    cokernel.π (ofLE A B h) ≫ (cokernelOfLEIsoOfEq hA hB h h').hom =
      ofLE B B' hB.le ≫ cokernel.π (ofLE A' B' h') := by
  subst hA hB
  simp [cokernelOfLEIsoOfEq, ofLE_refl]

/-- In a balanced preadditive category, the cokernel of an inclusion `B ≤ Z` of subobjects is zero
if and only if `B = Z`. -/
theorem isZero_cokernel_ofLE_iff [Preadditive C] [Balanced C] {B Z : Subobject X} (h : B ≤ Z)
    [HasCokernel (ofLE B Z h)] :
    IsZero (cokernel (ofLE B Z h)) ↔ B = Z := by
  rw [← Preadditive.epi_iff_isZero_cokernel]
  refine ⟨fun _ ↦ ?_, fun hEq ↦ ?_⟩
  · have : IsIso (ofLE B Z h) := isIso_of_mono_of_epi (ofLE B Z h)
    exact le_antisymm h (le_of_comm (inv (ofLE B Z h)) (by simp))
  · subst hEq
    rw [ofLE_refl]
    infer_instance

end CategoryTheory.Subobject
