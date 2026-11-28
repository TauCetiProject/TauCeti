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
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Unit and unitary norms, compact unitary groups, and norm rigidity

In a C⋆-ring, left and right multiplication by a unitary element preserve the norm
(`CStarRing.norm_coe_unitary_mul`, `CStarRing.norm_mul_coe_unitary`), so unitary conjugation
`x ↦ u * x * star u` preserves norms and norms of differences (`CStarRing.norm_unitary_conj`,
`CStarRing.norm_unitary_conj_sub`).

Every unitary element has norm at most one (`CStarRing.norm_le_one_of_mem_unitary`), and the
unitary elements form a closed set. So when the closed balls of the ring are compact, as for a
finite-dimensional C⋆-algebra such as the operators on a finite-dimensional inner product space,
its unitary group is compact. In particular the orthogonal and unitary groups of a
finite-dimensional real or complex inner product space are compact.

Because `‖star x * x‖ = ‖x‖ * ‖x‖` in any C⋆-ring, partial isometries have norm `≤ 1`, nonzero star
projections have norm `1`, and comparable star projections at distance `< 1` are equal.

## Main results

* `IsStarProjection.norm_eq_one`: a nonzero star projection of a C⋆-ring has norm `1`.
* `CStarRing.norm_one_le`: `‖1‖ ≤ 1` in any unital C⋆-ring, including the trivial one, where
  Mathlib's `CStarRing.norm_one` (which needs `Nontrivial`) does not apply.
* `CStarRing.norm_le_one_of_mem_unitary`: a unitary element has norm at most `1`, also in the
  trivial ring, where Mathlib's `CStarRing.norm_of_mem_unitary` does not apply.
* `CStarRing.norm_unitary_conj`: unitary conjugation preserves the norm in a C⋆-ring.
* `CStarRing.norm_unitary_conj_sub`: unitary conjugation preserves the norm of a difference in a
  C⋆-ring.
* `CStarRing.norm_inv_norm_sq_smul_star_mul_self`: normalizing `x⋆ x` by `‖x‖ ^ 2` gives an
  element of norm `1`.
* `CStarRing.isCompact_unitary`: the unitary elements of a proper C⋆-ring form a compact set.
* `CStarRing.instCompactSpaceUnitary`: the unitary group of a proper C⋆-ring is compact.
* `TauCeti.IsPartialIsometry.norm_le_one`,
  `IsStarProjection.eq_of_mul_eq_left_of_norm_sub_lt_one`,
  `IsStarProjection.eq_of_mul_eq_right_of_norm_sub_lt_one`: C⋆-ring norm rigidity.
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

/-- Normalizing `x⋆ x` by `‖x‖ ^ 2` gives an element of norm `1`. -/
theorem norm_inv_norm_sq_smul_star_mul_self [NormedSpace ℝ E] {x : E} (hx : x ≠ 0) :
    ‖(‖x‖ ^ 2)⁻¹ • (star x * x)‖ = 1 := by
  simp [norm_smul, norm_star_mul_self, ← sq, hx]

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

/-- Every partial isometry in a C⋆-ring has norm at most `1`. -/
theorem TauCeti.IsPartialIsometry.norm_le_one {E : Type*} [NonUnitalNormedRing E] [StarRing E]
    [CStarRing E] {v : E} (hv : IsPartialIsometry v) : ‖v‖ ≤ 1 := by
  have hle : ‖star v * v‖ ≤ 1 := hv.isStarProjection_star_mul_self.norm_le _
  rw [CStarRing.norm_star_mul_self] at hle; nlinarith [norm_nonneg v]

namespace IsStarProjection
variable {E : Type*} [NonUnitalNormedRing E] [StarRing E]

/-- Star projections `p, q` in a star normed ring with `p * q = p` and `‖p - q‖ < 1` satisfy
`p = q`. -/
theorem eq_of_mul_eq_left_of_norm_sub_lt_one {p q : E} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p * q = p) (h : ‖p - q‖ < 1) : p = q :=
  (sub_eq_zero.mp ((hp.sub_of_mul_eq_left hq hpq).isIdempotentElem.eq_zero_of_norm_lt_one
    (norm_sub_rev p q ▸ h))).symm

/-- Star projections `p, q` in a star normed ring with `q * p = p` and `‖p - q‖ < 1` satisfy
`p = q`. -/
theorem eq_of_mul_eq_right_of_norm_sub_lt_one {p q : E} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hqp : q * p = p) (h : ‖p - q‖ < 1) : p = q :=
  (sub_eq_zero.mp ((hp.sub_of_mul_eq_right hq hqp).isIdempotentElem.eq_zero_of_norm_lt_one
    (norm_sub_rev p q ▸ h))).symm

end IsStarProjection
