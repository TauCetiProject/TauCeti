/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The radial diffeomorphism `univBall` of a real inner product space

For `r > 0`, Mathlib's diffeomorphism `OpenPartialHomeomorph.univBall c r` of `E` onto the ball of
radius `r` about `c` is the radial map `x ↦ (r / √(1 + ‖x‖²)) • x`, followed by the translation to
`c`; for `r ≤ 0` it is just the translation by `c`, with target the whole space. Mathlib proves its
inverse smooth on the ball; `OpenPartialHomeomorph.contDiffOn_univBall_symm_target` states this on
the target of `univBall c r` for every `r`, so that it applies directly to charts built from
`univBall c r`.

The derivative of a general radial map `x ↦ g(‖x - x₀‖²) • (x - x₀)` is
`HasDerivAt.hasFDerivAt_smul_sub_norm_sq`.

## Main results

* `OpenPartialHomeomorph.contDiffOn_univBall_symm_target`: the inverse of `univBall c r` is
  smooth on its target.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace OpenPartialHomeomorph

/-- The inverse of `univBall c r` is smooth on its target, the ball of radius `r` about `c` if
`r > 0` and all of `E` otherwise. -/
theorem contDiffOn_univBall_symm_target {n : ℕ∞} (c : E) (r : ℝ) :
    ContDiffOn ℝ n (univBall c r).symm (univBall c r).target := by
  by_cases hr : 0 < r
  · rw [univBall_target _ hr]
    exact contDiffOn_univBall_symm
  · -- For `r ≤ 0`, `univBall c r` is the translation by `c`.
    simp only [univBall, hr, ↓reduceDIte]
    exact (contDiff_id.sub contDiff_const).contDiffOn

end OpenPartialHomeomorph
