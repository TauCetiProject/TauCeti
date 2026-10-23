/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Push

/-!
# Reassembling lower bounds from norm-splitting blocks

Suppose maps from one seminormed additive commutative group to another split the
squared extended norms of vectors. A common lower bound for the images of
each pair of vectors then gives the same bound for the original pair.

The maps need not be linear, continuous, or endomorphisms. Neither space
needs a definite norm or an inner product. The use of extended nonnegative
norms also avoids any summability or finiteness assumption on the index type.

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/BlockLowerBound.lean`.
-/

public section

open scoped ENNReal

namespace TauCeti

variable {H K : Type*} [SeminormedAddCommGroup H] [SeminormedAddCommGroup K]

/-- Reassemble a lower bound from a family of arbitrary maps that splits the
squared extended norms of the source space. The maps may take values in a
different seminormed additive commutative group. -/
theorem enorm_ge_of_blocks {c : ℝ≥0∞} {ι : Type*}
    (blocks : ι → H → K)
    (hsplit : ∀ f : H, ∑' i, ‖blocks i f‖ₑ ^ 2 = ‖f‖ₑ ^ 2)
    {x y : H} (hblock : ∀ i, c * ‖blocks i x‖ₑ ≤ ‖blocks i y‖ₑ) :
    c * ‖x‖ₑ ≤ ‖y‖ₑ := by
  have hsq : (c * ‖x‖ₑ) ^ 2 ≤ ‖y‖ₑ ^ 2 := by
    calc
      (c * ‖x‖ₑ) ^ 2 = c ^ 2 * ∑' i, ‖blocks i x‖ₑ ^ 2 := by
        rw [mul_pow, hsplit]
      _ = ∑' i, (c * ‖blocks i x‖ₑ) ^ 2 := by
        simp_rw [mul_pow]
        exact (ENNReal.tsum_mul_left).symm
      _ ≤ ∑' i, ‖blocks i y‖ₑ ^ 2 :=
        ENNReal.tsum_le_tsum fun i => by gcongr; exact hblock i
      _ = ‖y‖ₑ ^ 2 := hsplit _
  by_contra hcon
  push Not at hcon
  exact absurd ((ENNReal.pow_lt_pow_left_iff (n := 2) two_ne_zero).mpr hcon)
    (not_lt.mpr hsq)

end TauCeti
