/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RingTheory.Norm.Basic

/-!
# The real field norm of an `RCLike` field

For `z` in an `RCLike` field `𝕜`, the field norm `Algebra.norm ℝ z` has absolute value
`‖z‖ ^ finrank ℝ 𝕜`. This is the `RCLike` counterpart of Mathlib's `Algebra.norm_complex_apply`.

Its purpose is to move determinant estimates between `𝕜` and `ℝ`. By
`LinearMap.det_restrictScalars`, the real determinant of a `𝕜`-linear map, viewed as an
`ℝ`-linear map, is the field norm of its `𝕜`-determinant. This identity turns that field norm into
a power of the scalar norm, so real determinant bounds (for instance in terms of operator norms)
give the corresponding bounds over any `RCLike` field.

## Main results

* `TauCeti.RCLike.abs_algebraNorm_eq_norm_pow`: `|Algebra.norm ℝ z| = ‖z‖ ^ finrank ℝ 𝕜`.
-/

public section

open Module

namespace TauCeti

/-- The real field norm of `z` in an `RCLike` field `𝕜` has absolute value `‖z‖ ^ finrank ℝ 𝕜`. -/
theorem RCLike.abs_algebraNorm_eq_norm_pow {𝕜 : Type*} [RCLike 𝕜] (z : 𝕜) :
    |Algebra.norm ℝ z| = ‖z‖ ^ finrank ℝ 𝕜 := by
  -- Conjugation is an `ℝ`-algebra automorphism, so `N z ^ 2 = N (z * conj z)`, which is the
  -- norm of the real number `‖z‖ ^ 2`.
  have h : Algebra.norm ℝ z ^ 2 = (‖z‖ ^ finrank ℝ 𝕜) ^ 2 := by
    calc Algebra.norm ℝ z ^ 2
        = Algebra.norm ℝ z * Algebra.norm ℝ (RCLike.conjAe z) := by
          rw [Algebra.norm_eq_of_algEquiv, sq]
      _ = Algebra.norm ℝ (algebraMap ℝ 𝕜 (‖z‖ ^ 2)) := by
          rw [← map_mul, RCLike.conjAe_coe, RCLike.mul_conj, RCLike.algebraMap_eq_ofReal,
            RCLike.ofReal_pow]
      _ = (‖z‖ ^ finrank ℝ 𝕜) ^ 2 := by
          rw [Algebra.norm_algebraMap, ← pow_mul, ← pow_mul, mul_comm]
  rw [← sq_abs] at h
  exact (pow_left_inj₀ (abs_nonneg _) (by positivity) two_ne_zero).1 h

end TauCeti
