/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Affine images of functions on the upper half-plane

An affine image `A * f + B` that is injective on the upper half-plane must have `A ≠ 0`.
-/

public section

namespace TauCeti

open UpperHalfPlane Set

/-- An affine image of a function that is injective on the upper half-plane has a nonzero
linear coefficient. -/
theorem ne_zero_of_injOn_const_mul_add {R : Type*} [MulZeroClass R] [Add R] {f : ℂ → R}
    {A B : R} (h : InjOn (fun z => A * f z + B) upperHalfPlaneSet) : A ≠ 0 := by
  rintro rfl
  simpa using h (x₁ := Complex.I) (x₂ := 2 * Complex.I) (by simp) (by simp) (by simp)

end TauCeti
