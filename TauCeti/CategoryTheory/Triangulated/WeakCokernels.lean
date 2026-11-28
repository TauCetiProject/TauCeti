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

The first two arrows of a distinguished triangle form a weak cokernel pair. A
distinguished triangle in the opposite category also gives a weak cokernel pair in the
original category, which lets exactness on distinguished triangles detect flatness.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C]

/-- The second arrow of a distinguished triangle is a weak cokernel of its first arrow. -/
theorem isWeakCokernel_of_distTriang [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {T : Triangle C} (hT : T ∈ distTriang C) : TauCeti.IsWeakCokernel T.mor₁ T.mor₂ := by
  refine TauCeti.isWeakCokernel_iff.mpr ⟨comp_distTriang_mor_zero₁₂ T hT, fun _ k hk ↦ ?_⟩
  obtain ⟨l, hl⟩ := T.yoneda_exact₂ hT k hk
  exact ⟨l, hl.symm⟩

/-- The first two arrows of a distinguished triangle in the opposite category yield a weak
cokernel pair in the original category. -/
theorem isWeakCokernel_of_distTriang_op [HasZeroObject Cᵒᵖ] [HasShift Cᵒᵖ ℤ]
    [∀ n : ℤ, (shiftFunctor Cᵒᵖ n).Additive] [Pretriangulated Cᵒᵖ] {T : Triangle Cᵒᵖ}
    (hT : T ∈ distTriang Cᵒᵖ) : TauCeti.IsWeakCokernel T.mor₂.unop T.mor₁.unop := by
  simpa only [kernelForkOfDistTriangle, KernelFork.ι_ofι] using
    (isWeakLimitKernelForkOfDistTriangle T hT).isWeakCokernel

end CategoryTheory.Pretriangulated
