/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Kernel subobjects

This file records elementary characterizations of kernel subobjects.

## Main results

* `CategoryTheory.Limits.kernelSubobject_eq_top_iff`: the kernel subobject of a morphism `f` is `⊤`
  if and only if `f = 0`.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C]

/-- The kernel subobject of a morphism `f` is `⊤` if and only if `f = 0`. -/
@[simp]
lemma kernelSubobject_eq_top_iff [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    kernelSubobject f = ⊤ ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ kernelSubobject_zero⟩
  have hcomp : (⊤ : Subobject X).arrow ≫ f = 0 := by
    rw [← Subobject.ofLE_arrow h.symm.le, Category.assoc, kernelSubobject_arrow_comp, comp_zero]
  simpa using (cancel_epi (⊤ : Subobject X).arrow).1 (by simpa using hcomp)

end CategoryTheory.Limits
