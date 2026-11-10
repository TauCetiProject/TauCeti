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

On the real line the Laplacian is the second derivative, so the sine function and its rescalings
are eigenfunctions of `Δ`:

`Δ (fun y ↦ sin (a y)) x = -a ^ 2 * sin (a x)`.

These identities are not `@[simp]`: Mathlib's simp lemma
`InnerProductSpace.laplacian_eq_iteratedDeriv_real` rewrites `Δ` on `ℝ` to `iteratedDeriv 2`, so
their left-hand sides are not in simp normal form.

## Main declarations

* `TauCeti.laplacian_sin_const_mul`: `Δ (sin (a ·)) x = -a ^ 2 * sin (a x)`.
* `TauCeti.laplacian_sin`: `Δ sin x = -sin x`.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian

/-- On the real line, `x ↦ sin (a * x)` is an eigenfunction of the Laplacian with eigenvalue
`-a ^ 2`. -/
theorem laplacian_sin_const_mul (a x : ℝ) :
    Δ (fun y => Real.sin (a * y)) x = -a ^ 2 * Real.sin (a * x) := by
  rw [laplacian_eq_iteratedDeriv_real, iteratedDeriv_comp_const_mul Real.contDiff_sin]
  simp

/-- On the real line, `sin` is an eigenfunction of the Laplacian with eigenvalue `-1`. -/
theorem laplacian_sin (x : ℝ) : Δ Real.sin x = -Real.sin x := by
  rw [laplacian_eq_iteratedDeriv_real]
  simp

end TauCeti
