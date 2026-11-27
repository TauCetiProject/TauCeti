/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.WeakKernels
public import TauCeti.CategoryTheory.Limits.WeakLimits.WeakCokernels

/-!
# Weak cokernels from distinguished triangles

A distinguished triangle in the opposite category supplies a weak cokernel pair in the
original category. This lets exactness on distinguished triangles detect flatness.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject Cᵒᵖ] [HasShift Cᵒᵖ ℤ]
  [∀ n : ℤ, (shiftFunctor Cᵒᵖ n).Additive] [Pretriangulated Cᵒᵖ]

/-- The first two arrows of a distinguished triangle in the opposite category yield a weak
cokernel pair in the original category. -/
theorem isWeakCokernel_of_distTriang {T : Triangle Cᵒᵖ}
    (hT : T ∈ distTriang Cᵒᵖ) : TauCeti.IsWeakCokernel T.mor₂.unop T.mor₁.unop :=
  TauCeti.IsWeakCokernel.of_isWeakLimit (h := comp_distTriang_mor_zero₁₂ T hT)
    (isWeakLimitKernelForkOfDistTriangle T hT)

end CategoryTheory.Pretriangulated
