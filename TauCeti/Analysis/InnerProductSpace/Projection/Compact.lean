/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Compact boxes adapted to an orthogonal splitting

Let `K` be a subspace of a finite-dimensional inner product space `E`, so that every point splits
as `y = P_K y + P_{Kᗮ} y`. A set on which both components are bounded is bounded, since
`‖y‖ ≤ ‖P_K y‖ + ‖P_{Kᗮ} y‖`. This file records the resulting compactness of the closed *box*
`‖P_{Kᗮ} (y - x₀)‖ ≤ L`, `‖P_K y‖ ≤ R`, the domain of barrier arguments that treat the two
components separately.

## Main results

* `Submodule.isCompact_starProjection_box`: the box `‖P_{Kᗮ} (y - x₀)‖ ≤ L`, `‖P_K y‖ ≤ R` is
  compact.
-/

public section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The box `‖P_{Kᗮ} (y - x₀)‖ ≤ L`, `‖P_K y‖ ≤ R` is compact: it is closed, and bounded because
`y - x₀ = P_K (y - x₀) + P_{Kᗮ} (y - x₀)`. -/
theorem isCompact_starProjection_box (K : Submodule 𝕜 E) (x₀ : E) (L R : ℝ) :
    IsCompact ({y | ‖Kᗮ.starProjection (y - x₀)‖ ≤ L} ∩ {y | ‖K.starProjection y‖ ≤ R}) := by
  have := FiniteDimensional.proper_rclike 𝕜 E
  refine Metric.isCompact_of_isClosed_isBounded ((isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_le (by fun_prop) continuous_const)) ?_
  refine (Metric.isBounded_closedBall (x := x₀)
    (r := L + (R + ‖K.starProjection x₀‖))).subset fun y hy ↦ ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hP : ‖K.starProjection (y - x₀)‖ ≤ R + ‖K.starProjection x₀‖ := by
    rw [map_sub]
    exact (norm_sub_le _ _).trans (add_le_add_left hy.2 _)
  calc ‖y - x₀‖ = ‖K.starProjection (y - x₀) + Kᗮ.starProjection (y - x₀)‖ :=
        congrArg _ (K.starProjection_add_starProjection_orthogonal (y - x₀)).symm
    _ ≤ ‖K.starProjection (y - x₀)‖ + ‖Kᗮ.starProjection (y - x₀)‖ := norm_add_le _ _
    _ ≤ L + (R + ‖K.starProjection x₀‖) := by
      have hy1 : ‖Kᗮ.starProjection (y - x₀)‖ ≤ L := hy.1
      linarith

end Submodule
