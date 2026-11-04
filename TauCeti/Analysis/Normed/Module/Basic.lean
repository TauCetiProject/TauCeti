/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Basic facts about normed modules

The residual `y - z • x` changes by at most `‖z - w‖ * ‖x‖` when its scalar parameter
changes from `w` to `z`. This estimate is useful for perturbing approximate eigenvectors.

In a seminormed ring in which `ℤ` acts isometrically and `‖1‖ = 1`, such as `ℝ` or `ℂ`, the
cast `Int.castRingHom R` preserves norms. This makes lemmas stated for a `RingHomIsometric`
ring homomorphism, such as `Polynomial.supNorm_map`, apply to integer polynomials.
-/

public section

namespace TauCeti

/-- Changing a scalar parameter perturbs the residual by at most the scalar distance times
the norm of the vector. -/
theorem norm_sub_smul_le_norm_sub_smul_add {𝕜 E : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (y x : E) (z w : 𝕜) :
    ‖y - z • x‖ ≤ ‖y - w • x‖ + ‖z - w‖ * ‖x‖ := by
  have h := norm_sub_le_norm_sub_add_norm_sub y (w • x) (z • x)
  rwa [← sub_smul, norm_smul, norm_sub_rev w z] at h

end TauCeti

/-- The cast from `ℤ` is norm-preserving in a normed ring in which `ℤ` acts isometrically and
`‖1‖ = 1`, such as `ℝ` or `ℂ`. -/
instance RingHomIsometric.intCastRingHom {R : Type*} [SeminormedRing R]
    [NormSMulClass ℤ R] [NormOneClass R] : RingHomIsometric (Int.castRingHom R) where
  norm_map {n} := by simp [norm_intCast_eq_abs_mul_norm_one, Int.norm_eq_abs]

end
