/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# Basic identities and norm bounds for `RCLike` fields

## Main results

* `RCLike.re_eq_self_of_im_eq_zero`: a scalar with zero imaginary part equals its real part.
* `RCLike.norm_le_abs_re_add_abs_im`: `‖z‖ ≤ |re z| + |im z|`, the `RCLike` counterpart of
  `Complex.norm_le_abs_re_add_abs_im`.
* `RCLike.small`: every `RCLike` field is `Small` in any universe.
-/

public section

namespace RCLike

variable {K : Type*} [RCLike K]

universe u in
/-- Every `RCLike` field is `Small` in any universe, since `re` and `im` embed it into `ℝ × ℝ`. -/
instance (priority := 100) small : Small.{u} K :=
  small_of_injective (β := ℝ × ℝ) (f := fun z ↦ (re z, im z)) fun _ _ h ↦
    ext (congrArg Prod.fst h) (congrArg Prod.snd h)

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
