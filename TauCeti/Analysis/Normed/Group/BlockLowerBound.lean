/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Reassembling lower bounds from norm-splitting blocks

Suppose maps from one type with an extended norm to another split the `p`-th powers of the
extended norms of vectors, for some real `p > 0`; the case `p = 2` covers splittings of
squared norms such as orthogonal decompositions. A common lower bound for the images of each
pair of vectors then gives the same bound for the original pair.

The maps need not be linear, continuous, or endomorphisms, and the two types need carry no
structure beyond an extended norm `‖·‖ₑ`: no group structure, definite norm or inner product.
The use of extended nonnegative norms also avoids any summability or finiteness assumption on
the index type.

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/BlockLowerBound.lean`.
-/

public section

open scoped ENNReal

namespace TauCeti

variable {E F : Type*} [ENorm E] [ENorm F]

/-- Reassemble a lower bound from a family of arbitrary maps that splits the `p`-th powers
(`0 < p`) of the extended norms of the source. The maps may take values in a different type
with an extended norm. -/
theorem enorm_ge_of_blocks {ι : Type*} {p : ℝ} {c : ℝ≥0∞} (hp : 0 < p)
    (blocks : ι → E → F)
    (hsplit : ∀ f : E, ∑' i, ‖blocks i f‖ₑ ^ p = ‖f‖ₑ ^ p)
    {x y : E} (hblock : ∀ i, c * ‖blocks i x‖ₑ ≤ ‖blocks i y‖ₑ) :
    c * ‖x‖ₑ ≤ ‖y‖ₑ := by
  refine (ENNReal.rpow_le_rpow_iff hp).1 ?_
  calc
    (c * ‖x‖ₑ) ^ p = c ^ p * ∑' i, ‖blocks i x‖ₑ ^ p := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, hsplit]
    _ = ∑' i, (c * ‖blocks i x‖ₑ) ^ p := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le]
      exact ENNReal.tsum_mul_left.symm
    _ ≤ ∑' i, ‖blocks i y‖ₑ ^ p :=
      tsum_le_tsum fun i => ENNReal.rpow_le_rpow (hblock i) hp.le
    _ = ‖y‖ₑ ^ p := hsplit y

end TauCeti
