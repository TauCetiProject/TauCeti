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
# Normed star subgroups, C⋆-ring unit and projection norms, and compact unitary groups

In a C⋆-ring every unitary element has norm at most one (`CStarRing.norm_coe_unitary`), and the
unitary elements form a closed set. So when the closed balls of the ring are compact, as for a
finite-dimensional C⋆-algebra such as the operators on a finite-dimensional inner product space,
its unitary group is compact. In particular the orthogonal and unitary groups of a
finite-dimensional real or complex inner product space are compact.

Any additive subgroup closed under the involution of a `NormedStarGroup` inherits the restricted
`NormedStarGroup` structure.

## Main results

* `StarMemClass.instNormedStarGroup`: `NormedStarGroup` instance on star-closed additive subgroups.
* `CStarRing.norm_one_le`: `‖1‖ ≤ 1` in any unital C⋆-ring, including the trivial one, where
  Mathlib's `CStarRing.norm_one` (which needs `Nontrivial`) does not apply.
* `CStarRing.isCompact_unitary`: the unitary elements of a proper C⋆-ring form a compact set.
* `CStarRing.instCompactSpaceUnitary`: the unitary group of a proper C⋆-ring is compact.
* `IsStarProjection.norm_eq_one`, `TauCeti.IsPartialIsometry.norm_le_one`,
  `TauCeti.IsPartialIsometry.norm_eq_one`: C⋆-ring norm identities for projections and partial
  isometries.
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

section StarProjectionAndPartialIsometry
variable {E : Type*} [NonUnitalNormedRing E] [StarRing E] [CStarRing E]
/-- Every nonzero star projection in a C⋆-ring has norm `1`. -/
theorem IsStarProjection.norm_eq_one {e : E} (he : IsStarProjection e) (he0 : e ≠ 0) : ‖e‖ = 1 :=
  sub_eq_zero.mp <| (mul_eq_zero.mp <| by
    simp [mul_sub, ← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq,
      he.isIdempotentElem.eq]).resolve_left (norm_ne_zero_iff.mpr he0)
/-- Every partial isometry in a C⋆-ring is a contraction (`‖u‖ ≤ 1`). -/
theorem TauCeti.IsPartialIsometry.norm_le_one {u : E} (hu : TauCeti.IsPartialIsometry u) :
    ‖u‖ ≤ 1 := (sq_le_sq₀ (norm_nonneg u) zero_le_one).mp <| by
  simpa [sq, ← CStarRing.norm_star_mul_self] using
    IsStarProjection.norm_le _ hu.isStarProjection_star_mul_self
/-- Every nonzero partial isometry in a C⋆-ring has norm `1`. -/
theorem TauCeti.IsPartialIsometry.norm_eq_one {u : E} (hu : TauCeti.IsPartialIsometry u)
    (hu0 : u ≠ 0) : ‖u‖ = 1 := (sq_eq_sq₀ (norm_nonneg u) zero_le_one).mp <| by
  simpa [sq, ← CStarRing.norm_star_mul_self] using
    hu.isStarProjection_star_mul_self.norm_eq_one (mt star_mul_self_eq_zero.mp hu0)
end StarProjectionAndPartialIsometry
