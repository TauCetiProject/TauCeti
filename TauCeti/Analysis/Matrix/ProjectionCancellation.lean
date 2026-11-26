/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.MurrayVonNeumann
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.Cancellation
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Projection cancellation over `ℝ` and `ℂ`

Every `RCLike` field has projection cancellation (`TauCeti.hasProjectionCancellation_rclike`):
matrix projections over `ℝ` or `ℂ` are Murray–von Neumann equivalent exactly when they have the
same rank, and rank is additive on block sums.

## References

* M. Rørdam, Part I of Rørdam–Størmer, *Classification of Nuclear C⋆-Algebras. Entropy in
  Operator Algebras*, Encyclopaedia of Mathematical Sciences 126, Springer (2002), Section 1.3.
-/

public section

open Matrix

namespace TauCeti

/-- **Projection cancellation over `ℝ` and `ℂ`.** Every `RCLike` field `𝕜` has projection
cancellation: for matrix projections `p`, `q`, `r` over `𝕜`, `p ⊕ r ∼ q ⊕ r` implies `p ∼ q`. -/
theorem hasProjectionCancellation_rclike (𝕜 : Type*) [RCLike 𝕜] :
    HasProjectionCancellation 𝕜 := by
  refine hasProjectionCancellation_iff.2 fun k l j p q r hpqr ↦ ?_
  have hp := (isStarProjection_fromBlocks_zero₁₂_zero₂₁_iff.1 hpqr.isStarProjection_left).1
  have hq := (isStarProjection_fromBlocks_zero₁₂_zero₂₁_iff.1 hpqr.isStarProjection_right).1
  have e := hpqr.rank_eq
  rw [rank_fromBlocks_zero₁₂_zero₂₁, rank_fromBlocks_zero₁₂_zero₂₁] at e
  exact (isMurrayVonNeumannEquivalent_iff_rank_eq hp hq).2 (Nat.add_right_cancel e)

end TauCeti
