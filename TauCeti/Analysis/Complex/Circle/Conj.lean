/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle

/-!
# Complex conjugation and the action of the circle

A point `z` of the unit circle acts on `ℂ` by multiplication, and `conj z = z⁻¹`. So complex
conjugation intertwines the action of `z` with the action of `z⁻¹`:
`conj (z • w) = z⁻¹ • conj w` (`Circle.starRingEnd_smul`). This is what makes conjugation an
equivariant map from the circle representation on `ℂ` to its inverse, as used for the Hermitian
line of the inverse of a principal `U(1)`-bundle.
-/

public section

open ComplexConjugate

namespace Circle

/-- Complex conjugation intertwines multiplication by a point `z` of the circle with multiplication
by `z⁻¹`: `conj (z • w) = z⁻¹ • conj w`. -/
theorem starRingEnd_smul (z : Circle) (w : ℂ) : conj (z • w) = z⁻¹ • conj w := by
  simp [smul_def, ← coe_inv_eq_conj]

end Circle
