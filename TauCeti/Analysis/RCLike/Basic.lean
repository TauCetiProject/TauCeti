/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# Basic identities, norm bounds, and scalar continuity for `RCLike` fields

## Main results

* `RCLike.re_eq_self_of_im_eq_zero`: a scalar with zero imaginary part equals its real part.
* `RCLike.norm_le_abs_re_add_abs_im`: `‖z‖ ≤ |re z| + |im z|`, the `RCLike` counterpart of
  `Complex.norm_le_abs_re_add_abs_im`.
* `RCLike.continuousSMul`: joint continuity of scalar multiplication on a topological module over an
  `RCLike` field follows from continuity of the real action and of constant-scalar multiplication.
-/

public section

namespace RCLike

variable {K : Type*} [RCLike K]

/-- The norm of a scalar is at most the sum of the absolute values of its real and imaginary
parts. -/
theorem norm_le_abs_re_add_abs_im (z : K) : ‖z‖ ≤ |re z| + |im z| := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [norm_sq_eq_def]
  nlinarith [abs_mul_abs_self (re z), abs_mul_abs_self (im z), abs_nonneg (re z),
    abs_nonneg (im z)]

/-- A scalar with zero imaginary part is the image of its real part. -/
theorem re_eq_self_of_im_eq_zero {z : K} (h : im z = 0) : (re z : K) = z :=
  conj_eq_iff_re.mp (conj_eq_iff_im.mpr h)

/-- In a topological module over an `RCLike` field `K` with a compatible continuous real action,
joint continuity of the `K`-action follows from continuity of multiplication by each fixed scalar,
via `c • x = re c • x + im c • (I • x)`. -/
theorem continuousSMul {E : Type*} [AddCommMonoid E] [Module ℝ E] [Module K E]
    [IsScalarTower ℝ K E] [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    [ContinuousConstSMul K E] : ContinuousSMul K E where
  continuous_smul := by
    have h (p : K × E) : p.1 • p.2 = re p.1 • p.2 + im p.1 • ((I : K) • p.2) := by
      conv_lhs => rw [← re_add_im p.1]
      rw [add_smul, mul_smul]
      exact congr_arg₂ (· + ·) (algebraMap_smul K (re p.1) p.2)
        (algebraMap_smul K (im p.1) ((I : K) • p.2))
    exact (((continuous_re.comp continuous_fst).smul continuous_snd).add
      ((continuous_im.comp continuous_fst).smul
        ((continuous_const_smul (I : K)).comp continuous_snd))).congr fun p ↦ (h p).symm

end RCLike
