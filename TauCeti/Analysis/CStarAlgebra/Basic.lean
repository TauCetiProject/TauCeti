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
# Normed star subgroups, unit and unitary norms, and compact unitary groups

In a C⋆-ring, left and right multiplication by a unitary element preserve the norm
(`CStarRing.norm_coe_unitary_mul`, `CStarRing.norm_mul_coe_unitary`), so unitary conjugation
`x ↦ u * x * star u` preserves norms and norms of differences (`CStarRing.norm_unitary_conj`,
`CStarRing.norm_unitary_conj_sub`).

Every unitary element has norm at most one (`CStarRing.norm_coe_unitary`), and the unitary elements
form a closed set. So when the closed balls of the ring are compact, as for a finite-dimensional
C⋆-algebra such as the operators on a finite-dimensional inner product space, its unitary group is
compact. In particular the orthogonal and unitary groups of a finite-dimensional real or complex
inner product space are compact.

Any additive subgroup closed under the involution of a `NormedStarGroup` inherits the restricted
`NormedStarGroup` structure.

## Main results

* `StarMemClass.instNormedStarGroup`: `NormedStarGroup` instance on star-closed additive subgroups.
* `CStarRing.norm_one_le`: `‖1‖ ≤ 1` in any unital C⋆-ring, including the trivial one, where
  Mathlib's `CStarRing.norm_one` (which needs `Nontrivial`) does not apply.
* `CStarRing.norm_unitary_conj`: unitary conjugation preserves the norm in a C⋆-ring.
* `CStarRing.norm_unitary_conj_sub`: unitary conjugation preserves the norm of a difference in a
  C⋆-ring.
* `CStarRing.isCompact_unitary`: the unitary elements of a proper C⋆-ring form a compact set.
* `CStarRing.instCompactSpaceUnitary`: the unitary group of a proper C⋆-ring is compact.
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

/-- Conjugation by a unitary element in a C⋆-ring preserves the norm. -/
@[simp]
theorem norm_unitary_conj (u : unitary E) (x : E) :
    ‖(u : E) * x * star (u : E)‖ = ‖x‖ := by
  rw [← Unitary.coe_star, norm_mul_coe_unitary, norm_coe_unitary_mul]

/-- Conjugation by a unitary element in a C⋆-ring preserves the norm of a difference. -/
@[simp]
theorem norm_unitary_conj_sub (u : unitary E) (x y : E) :
    ‖(u : E) * x * star (u : E) - (u : E) * y * star (u : E)‖ = ‖x - y‖ := by
  rw [← sub_mul, ← mul_sub, norm_unitary_conj]

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
