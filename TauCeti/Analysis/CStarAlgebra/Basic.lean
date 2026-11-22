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
# Normed star subgroups, the unit of a C⋆-ring, compact unitary groups, and self-adjoint closures

In a C⋆-ring every unitary element has norm at most one (`CStarRing.norm_coe_unitary`), and the
unitary elements form a closed set. So when the closed balls of the ring are compact, as for a
finite-dimensional C⋆-algebra such as the operators on a finite-dimensional inner product space,
its unitary group is compact. In particular the orthogonal and unitary groups of a
finite-dimensional real or complex inner product space are compact.

Any additive subgroup closed under the involution of a `NormedStarGroup` inherits the restricted
`NormedStarGroup` structure. For any star-closed subobject `s` closed under addition and scalar
multiplication by a division semiring with `2 ≠ 0` inside a Hausdorff topological module with
continuous addition, continuous fixed-scalar multiplication, and continuous star, taking
self-adjoint parts commutes with topological closure (`StarMemClass.closure_inter_selfAdjoint`);
for a star-stable submodule (a star-closed additive submonoid closed under scalar multiplication) in
a normed star module over `ℝ` or `ℂ` with continuous star, intersecting the self-adjoint part with
a closed norm ball centred at `0` commutes with norm closure
(`StarMemClass.closure_inter_selfAdjoint_inter_closedBall_zero`).

## Main results

* `StarMemClass.instNormedStarGroup`: `NormedStarGroup` instance on star-closed additive subgroups.
* `CStarRing.norm_one_le`: `‖1‖ ≤ 1` in any unital C⋆-ring, including the trivial one, where
  Mathlib's `CStarRing.norm_one` (which needs `Nontrivial`) does not apply.
* `CStarRing.isCompact_unitary`: the unitary elements of a proper C⋆-ring form a compact set.
* `CStarRing.instCompactSpaceUnitary`: the unitary group of a proper C⋆-ring is compact.
* `StarMemClass.closure_inter_selfAdjoint`: taking self-adjoint parts commutes with topological
  closure.
* `StarMemClass.closure_inter_selfAdjoint_inter_closedBall_zero`: intersecting the self-adjoint
  part with a closed norm ball centred at `0` commutes with norm closure.
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

namespace StarMemClass

/-- Taking self-adjoint parts commutes with taking the closure of a star-closed subobject closed
under addition and scalar multiplication by a division semiring with `2 ≠ 0`, in a Hausdorff
topological module with continuous addition, continuous fixed-scalar multiplication, and continuous
star. -/
theorem closure_inter_selfAdjoint (𝕜 : Type*) {A S : Type*} [DivisionSemiring 𝕜]
    [NeZero (2 : 𝕜)] [TopologicalSpace A] [T2Space A] [AddCommGroup A] [StarAddMonoid A]
    [Module 𝕜 A] [ContinuousAdd A] [ContinuousConstSMul 𝕜 A] [ContinuousStar A]
    [SetLike S A] [AddMemClass S A] [SMulMemClass S 𝕜 A] [StarMemClass S A] (s : S) :
    closure ((s : Set A) ∩ selfAdjoint A) = closure (s : Set A) ∩ selfAdjoint A := by
  refine subset_antisymm
    (closure_inter_subset.trans
      (inter_subset_inter_right _ (isClosed_eq continuous_star continuous_id).closure_eq.subset))
    fun x ⟨hx, hxsa⟩ ↦ ?_
  have hre := map_mem_closure (f := fun a : A ↦ (2⁻¹ : 𝕜) • (a + star a)) (by fun_prop) hx
    (t := (s : Set A) ∩ selfAdjoint A) fun a ha ↦ by
      refine ⟨SMulMemClass.smul_mem _ (add_mem ha (star_mem ha)), ?_⟩
      simp only [SetLike.mem_coe, selfAdjoint.mem_iff]
      rw [← Nat.cast_two (R := 𝕜), star_inv_natCast_smul, (IsSelfAdjoint.add_star_self a).star_eq]
  have hx2 : (2⁻¹ : 𝕜) • (x + star x) = x := by
    rw [hxsa.star_eq, ← two_smul 𝕜 x, smul_smul, inv_mul_cancel₀ (NeZero.ne (2 : 𝕜)), one_smul]
  rwa [hx2] at hre

/-- Intersecting the self-adjoint part of a star-stable submodule (a star-closed additive submonoid
closed under scalar multiplication) with a closed norm ball centred at `0` commutes with taking the
norm closure, in a normed star module over `ℝ` or `ℂ` with continuous star. -/
theorem closure_inter_selfAdjoint_inter_closedBall_zero (𝕜 : Type*) {A S : Type*} [RCLike 𝕜]
    [NormedAddCommGroup A] [StarAddMonoid A] [NormedSpace 𝕜 A] [StarModule 𝕜 A]
    [ContinuousStar A] [SetLike S A] [AddSubmonoidClass S A] [SMulMemClass S 𝕜 A]
    [StarMemClass S A] (s : S) (r : ℝ) :
    closure ((s : Set A) ∩ selfAdjoint A ∩ closedBall 0 r) =
      closure (s : Set A) ∩ selfAdjoint A ∩ closedBall 0 r := by
  have hcl : closure ((s : Set A) ∩ selfAdjoint A) = closure (s : Set A) ∩ selfAdjoint A :=
    closure_inter_selfAdjoint 𝕜 s
  let _ : NormedSpace ℝ A := NormedSpace.restrictScalars ℝ 𝕜 A
  have _ : IsScalarTower ℝ 𝕜 A := RestrictScalars.isScalarTower ℝ 𝕜 A
  have _ : SMulMemClass S ℝ A := SMulMemClass.ofIsScalarTower S ℝ 𝕜 A
  have _ : StarModule ℝ A := ⟨fun c a ↦ by
    rw [← algebraMap_smul 𝕜 c a, star_smul, RCLike.algebraMap_eq_ofReal, RCLike.star_def,
      RCLike.conj_ofReal, ← RCLike.algebraMap_eq_ofReal, algebraMap_smul, star_trivial c]⟩
  let p : Submodule ℝ A := Submodule.ofClass s ⊓ selfAdjoint.submodule ℝ A
  have hp : (p : Set A) = (s : Set A) ∩ selfAdjoint A := by
    simp only [p, Submodule.coe_inf, Submodule.coe_ofClass,
      ← selfAdjoint.toAddSubgroup_submodule ℝ A, Submodule.coe_toAddSubgroup]
  rw [← hp, p.closure_inter_closedBall_zero r, hp, hcl]

end StarMemClass
