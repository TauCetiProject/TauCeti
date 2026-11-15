/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
import TauCeti.Algebra.Star.Basic

/-!
# Basic identities and norm bounds for `RCLike` fields

## Main results

* `RCLike.re_eq_self_of_im_eq_zero`: a scalar with zero imaginary part equals its real part.
* `RCLike.norm_le_abs_re_add_abs_im`: `‖z‖ ≤ |re z| + |im z|`, the `RCLike` counterpart of
  `Complex.norm_le_abs_re_add_abs_im`.
* `TauCeti.star_smul_mul_self`: `star (c • x) * (c • x) = (‖c‖ ^ 2 : ℝ) • (star x * x)` in any star
  module with compatible multiplication over an `RCLike` field `K`.
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

end RCLike

namespace TauCeti

/-- In a star algebra over an `RCLike` field `K`, `star (c • x) * (c • x)` scales `star x * x` by
`‖c‖ ^ 2`. -/
theorem star_smul_mul_self {K A : Type*} [RCLike K] [Mul A] [StarMul A] [MulAction K A] [SMul ℝ A]
    [IsScalarTower ℝ K A] [IsScalarTower K A A] [StarModule K A] (c : K) (x : A) :
    star (c • x) * (c • x) = (‖c‖ ^ 2 : ℝ) • (star x * x) := by
  rw [star_smul, smul_mul_assoc, TauCeti.mul_smul_comm_of_starModule, smul_smul,
    RCLike.star_def, mul_comm, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_alg,
    smul_one_smul]

end TauCeti
