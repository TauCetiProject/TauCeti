/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# Basic estimates for real or complex numbers

The norm of a real or complex number is at most the sum of the absolute values of its real and
imaginary parts. This is the `RCLike` form of Mathlib's `Complex.norm_le_abs_re_add_abs_im`; it
reduces estimates on the norm of a scalar to estimates on two real numbers of fixed sign.
-/

public section

namespace RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The norm of a real or complex number is at most the sum of the absolute values of its real
and imaginary parts. -/
theorem norm_le_abs_re_add_abs_im (z : 𝕜) : ‖z‖ ≤ |re z| + |im z| :=
  calc ‖z‖ = ‖(re z : 𝕜) + (im z : 𝕜) * I‖ := by rw [re_add_im]
    _ ≤ ‖(re z : 𝕜)‖ + ‖(im z : 𝕜) * I‖ := norm_add_le _ _
    _ ≤ |re z| + |im z| := by
      rw [norm_ofReal, norm_mul, norm_ofReal]
      gcongr
      refine mul_le_of_le_one_right (abs_nonneg _) ?_
      rw [norm_I]
      split_ifs <;> norm_num

end RCLike
