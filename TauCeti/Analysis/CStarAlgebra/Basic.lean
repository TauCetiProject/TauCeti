/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The unit of a C⋆-ring and compact unitary groups

In a C⋆-ring every unitary element has norm at most one
(`CStarRing.norm_le_one_of_mem_unitary`), and the unitary elements form a closed set. So when the
closed balls of the ring are compact, as for a finite-dimensional C⋆-algebra such as the
operators on a finite-dimensional inner product space, its unitary group is compact. In particular
the orthogonal and unitary groups of a finite-dimensional real or complex inner product space are
compact.

## Main results

* `IsStarProjection.norm_eq_one`: a nonzero star projection of a C⋆-ring has norm `1`.
* `CStarRing.norm_one_le`: `‖1‖ ≤ 1` in any unital C⋆-ring, including the trivial one, where
  Mathlib's `CStarRing.norm_one` (which needs `Nontrivial`) does not apply.
* `CStarRing.norm_le_one_of_mem_unitary`: a unitary element has norm at most `1`, also in the
  trivial ring, where Mathlib's `CStarRing.norm_of_mem_unitary` does not apply.
* `CStarRing.isCompact_unitary`: the unitary elements of a proper C⋆-ring form a compact set.
* `CStarRing.instCompactSpaceUnitary`: the unitary group of a proper C⋆-ring is compact.
-/

public section

/-- A nonzero star projection of a C⋆-ring has norm `1`: `‖e‖ = ‖e⋆ e‖ = ‖e‖ ^ 2`. -/
theorem IsStarProjection.norm_eq_one {E : Type*} [NonUnitalNormedRing E] [StarRing E]
    [CStarRing E] {e : E} (he : IsStarProjection e) (h : e ≠ 0) : ‖e‖ = 1 := by
  have h' : ‖e‖ * ‖e‖ = ‖e‖ := by
    rw [← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]
  exact (mul_eq_right₀ (norm_ne_zero_iff.mpr h)).mp h'

namespace CStarRing

variable {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]

/-- The unit of a C⋆-ring has norm at most `1`; it is `0` in the trivial ring and `1` otherwise. -/
theorem norm_one_le : ‖(1 : E)‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [Subsingleton.elim (1 : E) 0]
  · exact norm_one.le

/-- A unitary element of a C⋆-ring has norm at most `1`; it is `0` in the trivial ring and has
norm `1` otherwise. -/
theorem norm_le_one_of_mem_unitary {U : E} (hU : U ∈ unitary E) : ‖U‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [Subsingleton.elim U 0]
  · exact (norm_of_mem_unitary hU).le

variable [ProperSpace E]

/-- The unitary elements of a C⋆-ring with compact closed balls form a compact set. -/
theorem isCompact_unitary : IsCompact (unitary E : Set E) := by
  refine (isCompact_closedBall (0 : E) 1).of_isClosed_subset isClosed_unitary fun U hU ↦ ?_
  rw [mem_closedBall_zero_iff]
  exact norm_le_one_of_mem_unitary hU

/-- The unitary group of a C⋆-ring with compact closed balls is compact. -/
instance instCompactSpaceUnitary : CompactSpace (unitary E) :=
  isCompact_iff_compactSpace.1 isCompact_unitary

end CStarRing
