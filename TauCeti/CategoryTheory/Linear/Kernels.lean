/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Kernels of scalar multiples of the identity

In an `R`-linear category, the inclusion of any kernel fork of `m • 𝟙 X` is killed by `m`
(`CategoryTheory.Limits.KernelFork.smul_ι_eq_zero`).
-/

public section

namespace CategoryTheory.Limits.KernelFork

variable {R : Type*} [Semiring R] {C : Type*} [Category C] [Preadditive C] [Linear R C] {X : C}
  {m : R}

/-- The inclusion of a kernel fork of `m • 𝟙 X` is killed by `m`. -/
@[simp]
theorem smul_ι_eq_zero (c : KernelFork (m • 𝟙 X)) : m • c.ι = 0 := by
  simpa using c.condition

end CategoryTheory.Limits.KernelFork
