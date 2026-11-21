/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.MetricSpace.ProperSpace
public import TauCeti.Algebra.Star.PartialIsometry

/-!
# Normed star subgroups, the unit of a C⋆-ring, compact unitary groups, and norm rigidity

In a C⋆-ring every unitary element has norm at most one (`CStarRing.norm_coe_unitary`), and the
unitary elements form a closed set. So when the closed balls of the ring are compact, as for a
finite-dimensional C⋆-algebra such as the operators on a finite-dimensional inner product space,
its unitary group is compact. In particular the orthogonal and unitary groups of a
finite-dimensional real or complex inner product space are compact.

Any additive subgroup closed under the involution of a `NormedStarGroup` inherits the restricted
`NormedStarGroup` structure.

Because `‖star x * x‖ = ‖x‖ * ‖x‖` in any C⋆-ring, partial isometries have norm `≤ 1`, nonzero star
projections have norm `1`, and comparable star projections at distance `< 1` are equal.

## Main results

* `StarMemClass.instNormedStarGroup`: `NormedStarGroup` instance on star-closed additive subgroups.
* `CStarRing.norm_one_le`: `‖1‖ ≤ 1` in any unital C⋆-ring, including the trivial one, where
  Mathlib's `CStarRing.norm_one` (which needs `Nontrivial`) does not apply.
* `CStarRing.isCompact_unitary`: the unitary elements of a proper C⋆-ring form a compact set.
* `CStarRing.instCompactSpaceUnitary`: the unitary group of a proper C⋆-ring is compact.
* `TauCeti.IsPartialIsometry.norm_le_one`, `IsStarProjection.eq_zero_of_norm_lt_one`,
  `IsStarProjection.norm_eq_one_of_ne_zero`,
  `IsStarProjection.eq_of_mul_eq_left_of_norm_sub_lt_one`,
  `IsStarProjection.eq_of_mul_eq_right_of_norm_sub_lt_one`,
  `IsStarProjection.eq_one_of_norm_sub_one_lt_one`: C⋆-ring norm rigidity.
-/

public section

/-- Any additive subgroup closed under the involution of a `NormedStarGroup` inherits the
`NormedStarGroup` structure. -/
instance StarMemClass.instNormedStarGroup {S E : Type*} [SeminormedAddCommGroup E]
    [StarAddMonoid E] [NormedStarGroup E] [SetLike S E] [AddSubgroupClass S E] [StarMemClass S E]
    (s : S) : NormedStarGroup s where
  norm_star_le x := NormedStarGroup.norm_star_le (x : E)

namespace CStarRing

variable {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]

/-- The unit of a C⋆-ring has norm at most `1`; it is `0` in the trivial ring and `1` otherwise. -/
theorem norm_one_le : ‖(1 : E)‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · simp [Subsingleton.elim (1 : E) 0]
  · exact norm_one.le

variable [ProperSpace E]

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

/-- Every partial isometry in a C⋆-ring has norm at most `1`. -/
theorem TauCeti.IsPartialIsometry.norm_le_one {E : Type*} [NonUnitalNormedRing E] [StarRing E]
    [CStarRing E] {v : E} (hv : IsPartialIsometry v) : ‖v‖ ≤ 1 := by
  have hle : ‖star v * v‖ ≤ 1 := hv.isStarProjection_star_mul_self.norm_le _
  rw [CStarRing.norm_star_mul_self] at hle; nlinarith [norm_nonneg v]

namespace IsStarProjection
variable {E : Type*} [NonUnitalNormedRing E] [StarRing E] [CStarRing E]

/-- A star projection of norm strictly less than `1` in a C⋆-ring must be `0`. -/
theorem eq_zero_of_norm_lt_one {e : E} (he : IsStarProjection e) (h : ‖e‖ < 1) : e = 0 := by
  by_contra hne; have hsq : ‖e‖ * ‖e‖ = ‖e‖ := by
    rw [← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]
  nlinarith [norm_pos_iff.mpr hne]
/-- Every nonzero star projection in a C⋆-ring has norm `1`. -/
theorem norm_eq_one_of_ne_zero {e : E} (he : IsStarProjection e) (hne : e ≠ 0) : ‖e‖ = 1 :=
  le_antisymm (he.norm_le e) (not_lt.mp fun hlt ↦ hne (he.eq_zero_of_norm_lt_one hlt))
/-- Star projections `p, q` in a C⋆-ring with `p * q = p` and `‖p - q‖ < 1` satisfy `p = q`. -/
theorem eq_of_mul_eq_left_of_norm_sub_lt_one {p q : E} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p * q = p) (h : ‖p - q‖ < 1) : p = q :=
  (sub_eq_zero.mp ((hp.sub_of_mul_eq_left hq hpq).eq_zero_of_norm_lt_one
    (norm_sub_rev p q ▸ h))).symm
/-- Star projections `p, q` in a C⋆-ring with `q * p = p` and `‖p - q‖ < 1` satisfy `p = q`. -/
theorem eq_of_mul_eq_right_of_norm_sub_lt_one {p q : E} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hqp : q * p = p) (h : ‖p - q‖ < 1) : p = q :=
  (sub_eq_zero.mp ((hp.sub_of_mul_eq_right hq hqp).eq_zero_of_norm_lt_one
    (norm_sub_rev p q ▸ h))).symm
/-- A star projection at distance `< 1` from `1` in a unital C⋆-ring equals `1`. -/
theorem eq_one_of_norm_sub_one_lt_one {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]
    {p : E} (hp : IsStarProjection p) (h : ‖p - 1‖ < 1) : p = 1 :=
  hp.eq_of_mul_eq_left_of_norm_sub_lt_one (.one E) (mul_one p) h
end IsStarProjection
