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
# Normed star subgroups and compact unitary groups

In a C⋆-ring every unitary element has norm at most one (`CStarRing.norm_coe_unitary`), and the
unitary elements form a closed set. So when the closed balls of the ring are compact, as for a
finite-dimensional C⋆-algebra such as the operators on a finite-dimensional inner product space,
its unitary group is compact. In particular the orthogonal and unitary groups of a
finite-dimensional real or complex inner product space are compact.

Any additive subgroup closed under the involution of a `NormedStarGroup` inherits the restricted
`NormedStarGroup` structure. Finally, in a C⋆-ring, the C⋆-identity `‖e⋆ * e‖ = ‖e‖ ^ 2` forces
every star projection `e` to satisfy `‖e‖ ∈ {0, 1}`, isolating `0` and `1` among star projections
at norm distance `1`.

## Main results

* `StarMemClass.instNormedStarGroup`: `NormedStarGroup` instance on star-closed additive subgroups.
* `CStarRing.isCompact_unitary`: the unitary elements of a proper C⋆-ring form a compact set.
* `CStarRing.instCompactSpaceUnitary`: the unitary group of a proper C⋆-ring is compact.
* `IsStarProjection.norm_eq_zero_or_one`, `IsStarProjection.norm_eq_one`: a star projection in a
  C⋆-ring has norm `0` or `1`, and norm `1` whenever it is nonzero.
* `IsStarProjection.eq_zero_of_norm_lt_one`, `IsStarProjection.eq_one_of_norm_sub_one_lt_one`:
  a star projection in a C⋆-ring at distance strictly less than `1` from `0` or `1` equals `0` or
  `1`, respectively.
-/

public section

/-- Any additive subgroup closed under the involution of a `NormedStarGroup` inherits the
`NormedStarGroup` structure. -/
instance StarMemClass.instNormedStarGroup {S E : Type*} [SeminormedAddCommGroup E]
    [StarAddMonoid E] [NormedStarGroup E] [SetLike S E] [AddSubgroupClass S E] [StarMemClass S E]
    (s : S) : NormedStarGroup s where
  norm_star_le x := NormedStarGroup.norm_star_le (x : E)

namespace CStarRing

variable {E : Type*} [NormedRing E] [StarRing E] [CStarRing E] [ProperSpace E]

/-- The unitary elements of a C⋆-ring with compact closed balls form a compact set. -/
theorem isCompact_unitary : IsCompact (unitary E : Set E) := by
  refine (isCompact_closedBall (0 : E) 1).of_isClosed_subset isClosed_unitary fun U hU ↦ ?_
  rw [mem_closedBall_zero_iff]
  nontriviality E
  exact (norm_of_mem_unitary hU).le

/-- The unitary group of a C⋆-ring with compact closed balls is compact. -/
instance instCompactSpaceUnitary : CompactSpace (unitary E) :=
  isCompact_iff_compactSpace.1 isCompact_unitary

end CStarRing

namespace IsStarProjection

section NonUnital

variable {E : Type*} [NonUnitalNormedRing E] [StarRing E] [CStarRing E] {e : E}

/-- In a C⋆-ring, the norm of any star projection is either `0` or `1`. -/
theorem norm_eq_zero_or_one (he : IsStarProjection e) : ‖e‖ = 0 ∨ ‖e‖ = 1 := by
  have h : ‖e‖ * (‖e‖ - 1) = 0 := by
    simp [mul_sub, ← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]
  exact (mul_eq_zero.mp h).imp id sub_eq_zero.mp

/-- Every nonzero star projection in a C⋆-ring has norm `1`. -/
theorem norm_eq_one (he : IsStarProjection e) (he0 : e ≠ 0) : ‖e‖ = 1 :=
  he.norm_eq_zero_or_one.resolve_left (norm_ne_zero_iff.mpr he0)

/-- A star projection in a C⋆-ring of norm strictly less than `1` vanishes. -/
theorem eq_zero_of_norm_lt_one (he : IsStarProjection e) (h : ‖e‖ < 1) : e = 0 := by
  by_contra he0
  exact h.ne (he.norm_eq_one he0)

end NonUnital

/-- A star projection in a unital C⋆-ring at distance strictly less than `1` from `1` equals `1`. -/
theorem eq_one_of_norm_sub_one_lt_one {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]
    {e : E} (he : IsStarProjection e) (h : ‖e - 1‖ < 1) : e = 1 :=
  (sub_eq_zero.mp (he.one_sub.eq_zero_of_norm_lt_one (norm_sub_rev 1 e ▸ h))).symm

end IsStarProjection
