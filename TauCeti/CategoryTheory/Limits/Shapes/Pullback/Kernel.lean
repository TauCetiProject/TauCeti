/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Kernels as pullbacks

In a category with zero morphisms and a zero object, the kernel of `f : X ⟶ Y` is the pullback
of `f` along `0 ⟶ Y` (`CategoryTheory.IsPullback.kernel_ι`). Hence every class of morphisms
stable under base change contains `kernel f ⟶ 0` whenever it contains `f`; for instance the
kernel of a morphism with a right lifting property inherits that property.
-/

public section

namespace CategoryTheory.IsPullback

open Limits ZeroObject

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

/-- The kernel inclusion of `f : X ⟶ Y` is the base change of `f` along `0 ⟶ Y`. -/
lemma kernel_ι {X Y : C} (f : X ⟶ Y) [HasKernel f] :
    IsPullback (kernel.ι f) (0 : kernel f ⟶ 0) f (0 : 0 ⟶ Y) :=
  ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ kernel.lift f s.fst (by simp [s.condition]))
    (fun s ↦ by simp) (fun s ↦ (isZero_zero C).eq_of_tgt _ _) (fun s m hm _ ↦ by ext; simp [hm])⟩⟩

end CategoryTheory.IsPullback
