/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Manifold
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# Manifold differentiability of scaled Jacobi theta functions

Complements `Mathlib.NumberTheory.ModularForms.JacobiTheta.Manifold` with manifold
holomorphy of `w ↦ jacobiTheta (m * (w : ℂ))` on the upper half-plane `ℍ` for every natural
number `m`.

## Main results

* `TauCeti.mdifferentiable_jacobiTheta_natCast_mul`: `w ↦ jacobiTheta (m * (w : ℂ))` is
  holomorphic on `ℍ` for every natural number `m`.
-/

public section

open Complex
open scoped Manifold UpperHalfPlane

namespace TauCeti

/-- The scaled theta function `w ↦ jacobiTheta (m * (w : ℂ))` is holomorphic on `ℍ` for every
natural number `m` (being constant at `m = 0`). -/
theorem mdifferentiable_jacobiTheta_natCast_mul (m : ℕ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun w : ℍ ↦ jacobiTheta (m * (w : ℂ))) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simpa using mdifferentiable_const (c := jacobiTheta 0)
  · intro w
    have hm_im : 0 < ((m : ℂ) * (w : ℂ)).im := by
      simpa using mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) w.im_pos
    have hmul : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ ↦ (m : ℂ) * (z : ℂ)) w :=
      ((differentiableAt_id : DifferentiableAt ℂ id (w : ℂ)).const_mul
        (m : ℂ)).mdifferentiableAt.comp w (UpperHalfPlane.mdifferentiable_coe w)
    exact (differentiableAt_jacobiTheta hm_im).mdifferentiableAt.comp w hmul

end TauCeti
