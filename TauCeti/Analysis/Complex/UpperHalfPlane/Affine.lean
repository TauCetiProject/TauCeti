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

open Complex UpperHalfPlane Set

/-- An affine image of a function that is injective on the upper half-plane has a nonzero
linear coefficient. -/
theorem ne_zero_of_injOn_const_mul_add {f : ℂ → ℂ} {A B : ℂ}
    (h : InjOn (fun z => A * f z + B) upperHalfPlaneSet) : A ≠ 0 := by
  intro hA
  have hne := h (show Complex.I ∈ upperHalfPlaneSet by simp [upperHalfPlaneSet])
    (show 2 * Complex.I ∈ upperHalfPlaneSet by simp [upperHalfPlaneSet]) (by simp [hA])
  norm_num at hne

end TauCeti
