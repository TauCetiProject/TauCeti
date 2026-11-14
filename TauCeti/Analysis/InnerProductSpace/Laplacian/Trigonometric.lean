/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# The Laplacian of the sine function

On the real line the Laplacian is the second derivative, so for every `a : ℝ`

`Δ (fun y ↦ sin (a y)) x = -a ^ 2 * sin (a x)`.

For `a ≠ 0` this says that `y ↦ sin (a y)` is an eigenfunction of `Δ` with eigenvalue `-a ^ 2`;
for `a = 0` both sides vanish.

This identity is not `@[simp]`: Mathlib's simp lemma
`InnerProductSpace.laplacian_eq_iteratedDeriv_real` rewrites `Δ` on `ℝ` to `iteratedDeriv 2`, so
its left-hand side is not in simp normal form.

## Main declarations

* `TauCeti.laplacian_sin_const_mul`: `Δ (sin (a ·)) x = -a ^ 2 * sin (a x)`.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian

/-- On the real line, the Laplacian of `x ↦ sin (a * x)` is `-a ^ 2 * sin (a * x)`. For `a ≠ 0`,
this makes `x ↦ sin (a * x)` an eigenfunction of `Δ` with eigenvalue `-a ^ 2`. -/
theorem laplacian_sin_const_mul (a x : ℝ) :
    Δ (fun y => Real.sin (a * y)) x = -a ^ 2 * Real.sin (a * x) := by
  rw [laplacian_eq_iteratedDeriv_real, iteratedDeriv_comp_const_mul Real.contDiff_sin]
  simp

end TauCeti
