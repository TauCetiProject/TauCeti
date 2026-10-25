/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.Linarith

/-!
# Norms of combinations with coefficients in `[0, 1]`

For `x, y ∈ [0, 1]` and vectors `a`, `b` in a real normed space,
`‖x • b + y • a‖ + ‖(1 - y) • a + (1 - x) • b‖ ≤ ‖a‖ + ‖b‖`. The two vectors on the left are the
derivatives of the product `u v` and of `u + v - u v` at a point where `u = x`, `v = y`, `Du = a`
and `Dv = b`, so this is the pointwise inequality behind the submodularity of the perimeter.
-/

public section

namespace TauCeti

open Set

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- For `x, y ∈ [0, 1]`, the vectors `x • b + y • a` and `(1 - y) • a + (1 - x) • b` have total
norm at most `‖a‖ + ‖b‖`. -/
theorem norm_smul_add_add_norm_smul_add_le {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) (a b : E) :
    ‖x • b + y • a‖ + ‖(1 - y) • a + (1 - x) • b‖ ≤ ‖a‖ + ‖b‖ := by
  have h₁ := norm_add_le (x • b) (y • a)
  have h₂ := norm_add_le ((1 - y) • a) ((1 - x) • b)
  rw [norm_smul_of_nonneg hx.1, norm_smul_of_nonneg hy.1] at h₁
  rw [norm_smul_of_nonneg (sub_nonneg.2 hy.2), norm_smul_of_nonneg (sub_nonneg.2 hx.2)] at h₂
  linarith

end TauCeti
