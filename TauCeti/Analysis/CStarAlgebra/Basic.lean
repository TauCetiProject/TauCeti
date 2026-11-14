/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.MetricSpace.ProperSpace
import TauCeti.Analysis.Normed.Module.Ball.StarConvex

/-!
# Normed star subgroups, compact unitary groups, and self-adjoint closures

In a C⋆-ring every unitary element has norm at most one (`CStarRing.norm_coe_unitary`), and the
unitary elements form a closed set. So when the closed balls of the ring are compact, as for a
finite-dimensional C⋆-algebra such as the operators on a finite-dimensional inner product space,
its unitary group is compact. In particular the orthogonal and unitary groups of a
finite-dimensional real or complex inner product space are compact.

Any additive subgroup closed under the involution of a `NormedStarGroup` inherits the restricted
`NormedStarGroup` structure. For a star subalgebra `S` over `ℝ` or `ℂ`, taking self-adjoint parts
and intersecting with closed norm balls centred at `0` both commute with topological closure.

## Main results

* `StarMemClass.instNormedStarGroup`: `NormedStarGroup` instance on star-closed additive subgroups.
* `CStarRing.isCompact_unitary`: the unitary elements of a proper C⋆-ring form a compact set.
* `CStarRing.instCompactSpaceUnitary`: the unitary group of a proper C⋆-ring is compact.
* `StarSubalgebra.closure_inter_selfAdjoint` and
  `StarSubalgebra.closure_inter_selfAdjoint_inter_closedBall_zero`: self-adjoint parts and closed
  balls of star subalgebras commute with topological closure.
-/

public section

open Metric Set

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

namespace StarSubalgebra

/-- Taking self-adjoint parts commutes with taking the closure of a star subalgebra over `ℝ` or
`ℂ`. -/
theorem closure_inter_selfAdjoint {𝕜 A : Type*} [RCLike 𝕜] [TopologicalSpace A] [T2Space A]
    [Ring A] [StarRing A] [Algebra 𝕜 A] [StarModule 𝕜 A] [ContinuousAdd A]
    [ContinuousConstSMul 𝕜 A] [ContinuousStar A] (S : StarSubalgebra 𝕜 A) :
    closure ((S : Set A) ∩ selfAdjoint A) = closure (S : Set A) ∩ selfAdjoint A := by
  refine subset_antisymm
    (closure_inter_subset.trans
      (inter_subset_inter_right _ (isClosed_eq continuous_star continuous_id).closure_eq.subset))
    fun x ⟨hx, hxsa⟩ ↦ ?_
  have h2 : IsSelfAdjoint (2⁻¹ : 𝕜) := by simp [IsSelfAdjoint]
  have hre := map_mem_closure (f := fun a : A ↦ (2⁻¹ : 𝕜) • (a + star a)) (by fun_prop) hx
    (t := (S : Set A) ∩ selfAdjoint A) fun a ha ↦
      ⟨SMulMemClass.smul_mem _ (add_mem ha (star_mem ha)), h2.smul (.add_star_self a)⟩
  have hx2 : (2⁻¹ : 𝕜) • (x + star x) = x := by
    rw [hxsa.star_eq, ← two_smul 𝕜 x, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  rwa [hx2] at hre

/-- Intersecting the self-adjoint part of a star subalgebra with a closed norm ball centred at `0`
commutes with taking the norm closure. -/
theorem closure_inter_selfAdjoint_inter_closedBall_zero {𝕜 A : Type*} [RCLike 𝕜] [NormedRing A]
    [StarRing A] [NormedAlgebra 𝕜 A] [NormedSpace ℝ A] [IsScalarTower ℝ 𝕜 A] [StarModule 𝕜 A]
    [ContinuousStar A] (S : StarSubalgebra 𝕜 A) (r : ℝ) :
    closure ((S : Set A) ∩ selfAdjoint A ∩ closedBall 0 r) =
      closure (S : Set A) ∩ selfAdjoint A ∩ closedBall 0 r := by
  have : StarModule ℝ A := ⟨fun c a ↦ by
    simp only [RCLike.real_smul_eq_coe_smul (K := 𝕜), star_smul, RCLike.star_def,
      RCLike.conj_ofReal, star_trivial]⟩
  let p : Submodule ℝ A :=
    (S.toSubalgebra.toSubmodule.restrictScalars ℝ) ⊓ selfAdjoint.submodule ℝ A
  have hp : (p : Set A) = (S : Set A) ∩ selfAdjoint A := rfl
  rw [← hp, p.closure_inter_closedBall_zero r, hp, S.closure_inter_selfAdjoint]

end StarSubalgebra
