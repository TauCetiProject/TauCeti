/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# The integer cast into a normed ring

In a seminormed ring in which `ℤ` acts isometrically and `‖1‖ = 1`, such as `ℝ` or `ℂ`, the
cast `Int.castRingHom R` preserves norms. This makes lemmas stated for a `RingHomIsometric`
ring homomorphism, such as `Polynomial.supNorm_map`, apply to integer polynomials.
-/

public section

/-- The cast from `ℤ` is norm-preserving in a normed ring in which `ℤ` acts isometrically and
`‖1‖ = 1`, such as `ℝ` or `ℂ`. -/
instance RingHomIsometric.intCastRingHom {R : Type*} [SeminormedRing R]
    [NormSMulClass ℤ R] [NormOneClass R] : RingHomIsometric (Int.castRingHom R) where
  norm_map {n} := by simp [norm_intCast_eq_abs_mul_norm_one, Int.norm_eq_abs]

end
