/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The defect form of a bounded operator

For a bounded operator `X : F →L[𝕜] E` between inner product spaces, the real form
`(v, w) ↦ ‖X‖² re ⟪v, w⟫ - re ⟪X v, X w⟫` is positive semidefinite, since its diagonal value
`‖X‖² ‖v‖² - ‖X v‖²` is nonnegative by the definition of the operator norm. It therefore satisfies
the Cauchy–Schwarz inequality. If a unit vector `v` nearly attains the norm of `X`, this makes
`re ⟪X w, X v⟫` close to `‖X‖² re ⟪w, v⟫`, with an error of at most
`‖X‖ ‖w‖ √(‖X‖² - ‖X v‖²)`.

## Main statements

* `ContinuousLinearMap.sq_opNorm_sq_mul_re_inner_sub_re_inner_le`: the Cauchy–Schwarz inequality
  for the defect form of an operator.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Cauchy–Schwarz for the defect form of an operator.** For `X : F →L[𝕜] E`, the real form
`(v, w) ↦ ‖X‖² re ⟪v, w⟫ - re ⟪X v, X w⟫` is positive semidefinite, so it satisfies the
Cauchy–Schwarz inequality. In particular, for a unit vector `v`, `re ⟪X w, X v⟫` differs from
`‖X‖² re ⟪w, v⟫` by at most `‖X‖ ‖w‖ √(‖X‖² - ‖X v‖²)`. -/
theorem sq_opNorm_sq_mul_re_inner_sub_re_inner_le (X : F →L[𝕜] E) (v w : F) :
    (‖X‖ ^ 2 * RCLike.re ⟪v, w⟫_𝕜 - RCLike.re ⟪X v, X w⟫_𝕜) ^ 2 ≤
      (‖X‖ ^ 2 * ‖v‖ ^ 2 - ‖X v‖ ^ 2) * (‖X‖ ^ 2 * ‖w‖ ^ 2 - ‖X w‖ ^ 2) := by
  -- The defect form is nonnegative on `v + t w`, a quadratic in `t : ℝ`.
  have h (t : ℝ) : 0 ≤ (‖X‖ ^ 2 * ‖w‖ ^ 2 - ‖X w‖ ^ 2) * (t * t) +
      2 * (‖X‖ ^ 2 * RCLike.re ⟪v, w⟫_𝕜 - RCLike.re ⟪X v, X w⟫_𝕜) * t +
      (‖X‖ ^ 2 * ‖v‖ ^ 2 - ‖X v‖ ^ 2) := by
    have h₁ : ‖X (v + (t : 𝕜) • w)‖ ^ 2 ≤ (‖X‖ * ‖v + (t : 𝕜) • w‖) ^ 2 := by
      gcongr
      exact X.le_opNorm _
    rw [map_add, map_smul, mul_pow, norm_add_sq (𝕜 := 𝕜), norm_add_sq (𝕜 := 𝕜)] at h₁
    simp only [inner_smul_real_right, norm_smul, RCLike.norm_ofReal, mul_pow, sq_abs,
      RCLike.smul_re] at h₁
    nlinarith
  have := discrim_le_zero h
  rw [discrim] at this
  nlinarith

end ContinuousLinearMap
