/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Pythagoras for a symmetric projection

A symmetric idempotent endomorphism `p` of an inner product space
(`LinearMap.IsSymmetricProjection`) is an orthogonal projection, so it splits every vector
orthogonally: `‖y‖² = ‖p y‖² + ‖(1 - p) y‖²`.
This is the operator form of Mathlib's `Submodule.norm_sq_eq_add_norm_sq_projection`, stated for
the operator `p` instead of a subspace with an orthogonal projection.

## Main results

* `LinearMap.IsSymmetricProjection.norm_sq_eq_add_norm_sq`: `‖y‖² = ‖p y‖² + ‖(1 - p) y‖²`.
-/

public section

open scoped InnerProductSpace

namespace LinearMap.IsSymmetricProjection

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A symmetric projection `p` splits the squared norm orthogonally:
`‖y‖² = ‖p y‖² + ‖(1 - p) y‖²`. -/
theorem norm_sq_eq_add_norm_sq {p : E →ₗ[𝕜] E} (hp : p.IsSymmetricProjection) (y : E) :
    ‖y‖ ^ 2 = ‖p y‖ ^ 2 + ‖(1 - p) y‖ ^ 2 := by
  have h_orth : ⟪p y, (1 - p) y⟫_𝕜 = 0 := by
    rw [hp.isSymmetric, ← mul_apply_eq_comp, hp.isIdempotentElem.mul_one_sub_self,
      LinearMap.zero_apply, inner_zero_right]
  simpa [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h_orth

end LinearMap.IsSymmetricProjection
