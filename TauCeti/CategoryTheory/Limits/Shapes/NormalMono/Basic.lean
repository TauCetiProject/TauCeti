/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Basic

/-!
# Normal monomorphisms

Every normal monomorphism `f : X ⟶ Y` having a cokernel is a kernel of its cokernel projection
(`CategoryTheory.NormalMono.isLimitKernelForkCokernelπ`).
-/

public section

namespace CategoryTheory

open Limits

universe v u

/-- Every normal monomorphism is a kernel of its cokernel projection. -/
noncomputable def NormalMono.isLimitKernelForkCokernelπ {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [hf : NormalMono f] [HasCokernel f] :
    IsLimit (KernelFork.ofι f (cokernel.condition f)) :=
  isKernelOfComp (cokernel.desc f hf.g hf.w) hf.g hf.isLimit
    (cokernel.condition f) (cokernel.π_desc f hf.g hf.w)

end CategoryTheory
