/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Algebra.Star.BigOperators

/-!
# Normed star subgroups, unit and unitary norms, compact unitary groups, and C⋆-ring sum bounds

In a C⋆-ring, left and right multiplication by a unitary element preserve the norm
(`CStarRing.norm_coe_unitary_mul`, `CStarRing.norm_mul_coe_unitary`), so unitary conjugation
`x ↦ u * x * star u` preserves norms and norms of differences (`CStarRing.norm_unitary_conj`,
`CStarRing.norm_unitary_conj_sub`).

Every unitary element has norm at most one (`CStarRing.norm_le_one_of_mem_unitary`), and the
unitary elements form a closed set. So when the closed balls of the ring are compact, as for a
finite-dimensional C⋆-algebra such as the operators on a finite-dimensional inner product space,
its unitary group is compact. In particular the orthogonal and unitary groups of a
finite-dimensional real or complex inner product space are compact.

Any additive subgroup closed under the involution of a `NormedStarGroup` inherits the restricted
`NormedStarGroup` structure.

In any C⋆-ring, expanding `‖∑ i ∈ s, d i‖ ^ 2 = ‖star (∑ i ∈ s, d i) * ∑ j ∈ s, d j‖` bounds the
squared norm of a finite sum in terms of uniform diagonal norm bounds `‖d i‖ ≤ C` and off-diagonal
bounds `‖star (d i) * d j‖ ≤ η` (`TauCeti.CStarAlgebra.norm_sum_sq_le`).

## Main results

* `StarMemClass.instNormedStarGroup`: `NormedStarGroup` instance on star-closed additive subgroups.
* `IsStarProjection.norm_eq_one`: a nonzero star projection of a C⋆-ring has norm `1`.
* `CStarRing.norm_one_le`: `‖1‖ ≤ 1` in any unital C⋆-ring, including the trivial one, where
  Mathlib's `CStarRing.norm_one` (which needs `Nontrivial`) does not apply.
* `CStarRing.norm_le_one_of_mem_unitary`: a unitary element has norm at most `1`, also in the
  trivial ring, where Mathlib's `CStarRing.norm_of_mem_unitary` does not apply.
* `CStarRing.norm_unitary_conj`: unitary conjugation preserves the norm in a C⋆-ring.
* `CStarRing.norm_unitary_conj_sub`: unitary conjugation preserves the norm of a difference in a
  C⋆-ring.
* `CStarRing.isCompact_unitary`: the unitary elements of a proper C⋆-ring form a compact set.
* `CStarRing.instCompactSpaceUnitary`: the unitary group of a proper C⋆-ring is compact.
* `TauCeti.CStarAlgebra.norm_sum_sq_le`: C⋆-identity bound on the squared norm of a finite sum in a
  C⋆-ring with bounded diagonal norms and off-diagonal products `star (d i) * d j`.
* `TauCeti.CStarAlgebra.norm_average_sq_le`: C⋆-identity bound on the squared norm of an
  equal-weight finite average in a C⋆-ring.
-/

public section

/-- Any additive subgroup closed under the involution of a `NormedStarGroup` inherits the
`NormedStarGroup` structure. -/
instance StarMemClass.instNormedStarGroup {S E : Type*} [SeminormedAddCommGroup E]
    [StarAddMonoid E] [NormedStarGroup E] [SetLike S E] [AddSubgroupClass S E] [StarMemClass S E]
    (s : S) : NormedStarGroup s where
  norm_star_le x := NormedStarGroup.norm_star_le (x : E)

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

namespace TauCeti.CStarAlgebra

/-- C⋆-identity estimate on the squared norm of a finite sum in a C⋆-ring: if every term `d i`
(`i ∈ s`) has norm at most `C` and every off-diagonal product `star (d i) * d j` (`i ≠ j`) has norm
at most `η` (`0 ≤ η`), then `‖∑ i ∈ s, d i‖ ^ 2 ≤ s.card * C ^ 2 + s.card ^ 2 * η`. -/
theorem norm_sum_sq_le {A ι : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    {s : Finset ι} {d : ι → A} {C η : ℝ} (hη : 0 ≤ η)
    (hd : ∀ i ∈ s, ‖d i‖ ≤ C)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ‖star (d i) * d j‖ ≤ η) :
    ‖∑ i ∈ s, d i‖ ^ 2 ≤ (s.card : ℝ) * C ^ 2 + (s.card : ℝ) ^ 2 * η := by
  classical
  have hterm : ∀ i ∈ s, ∀ j ∈ s,
      ‖star (d i) * d j‖ ≤ (if i = j then C ^ 2 else 0) + η := by
    intro i hi j hj
    split_ifs with hij
    · subst hij
      rw [CStarRing.norm_star_mul_self, ← sq]
      exact (pow_le_pow_left₀ (norm_nonneg _) (hd i hi) 2).trans (le_add_of_nonneg_right hη)
    · simpa only [zero_add] using hoff i hi j hj hij
  calc ‖∑ i ∈ s, d i‖ ^ 2
      = ‖∑ i ∈ s, ∑ j ∈ s, star (d i) * d j‖ := by
        rw [sq, ← CStarRing.norm_star_mul_self, star_sum, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ‖star (d i) * d j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ i ∈ s, ∑ j ∈ s, ((if i = j then C ^ 2 else 0) + η) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
    _ = (s.card : ℝ) * C ^ 2 + (s.card : ℝ) ^ 2 * η := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const, nsmul_eq_mul]
        rw [Finset.sum_ite_of_true fun _ hx => hx, Finset.sum_const, nsmul_eq_mul]
        ring

/-- C⋆-identity estimate on the squared norm of an equal-weight average in a C⋆-ring: if every
term `d i` (`i ∈ s`) has norm at most `C` and every off-diagonal product `star (d i) * d j`
(`i ≠ j`) has norm at most `η` (`0 ≤ η`), then
`‖(s.card : ℝ)⁻¹ • ∑ i ∈ s, d i‖ ^ 2 ≤ C ^ 2 / s.card + η`. -/
theorem norm_average_sq_le {A ι : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    [SMulZeroClass ℝ A] [IsBoundedSMul ℝ A]
    {s : Finset ι} {d : ι → A} {C η : ℝ} (hη : 0 ≤ η) (hd : ∀ i ∈ s, ‖d i‖ ≤ C)
    (hoff : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ‖star (d i) * d j‖ ≤ η) :
    ‖(s.card : ℝ)⁻¹ • ∑ i ∈ s, d i‖ ^ 2 ≤ C ^ 2 / s.card + η := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hη
  have hsmul : ‖(s.card : ℝ)⁻¹ • ∑ i ∈ s, d i‖ ^ 2 ≤
      ((s.card : ℝ)⁻¹) ^ 2 * ‖∑ i ∈ s, d i‖ ^ 2 := by
    calc ‖(s.card : ℝ)⁻¹ • ∑ i ∈ s, d i‖ ^ 2
        ≤ (‖(s.card : ℝ)⁻¹‖ * ‖∑ i ∈ s, d i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_smul_le _ _) 2
      _ = ((s.card : ℝ)⁻¹) ^ 2 * ‖∑ i ∈ s, d i‖ ^ 2 := by
          rw [Real.norm_of_nonneg (by positivity), mul_pow]
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_pos.ne'
  calc ‖(s.card : ℝ)⁻¹ • ∑ i ∈ s, d i‖ ^ 2
      ≤ ((s.card : ℝ)⁻¹) ^ 2 * ‖∑ i ∈ s, d i‖ ^ 2 := hsmul
    _ ≤ ((s.card : ℝ)⁻¹) ^ 2 * ((s.card : ℝ) * C ^ 2 + (s.card : ℝ) ^ 2 * η) :=
        mul_le_mul_of_nonneg_left (norm_sum_sq_le hη hd hoff) (by positivity)
    _ = C ^ 2 / s.card + η := by field_simp

end TauCeti.CStarAlgebra
