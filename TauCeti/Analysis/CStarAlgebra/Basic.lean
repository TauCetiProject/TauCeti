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

/-!
# Normed star subgroups and compact unitary groups

In a C⋆-ring every unitary element has norm at most one (`CStarRing.norm_coe_unitary`), and the
unitary elements form a closed set. So when the closed balls of the ring are compact, as for a
finite-dimensional C⋆-algebra such as the operators on a finite-dimensional inner product space,
its unitary group is compact. In particular the orthogonal and unitary groups of a
finite-dimensional real or complex inner product space are compact.

Any additive subgroup closed under the involution of a `NormedStarGroup` inherits the restricted
`NormedStarGroup` structure. In a normed space over `ℝ` or `ℂ` with a continuous involution, the
self-adjoint elements of norm at most `r` of a star-closed submodule are dense in those of its
closure: take real parts, then rescale them into the ball.

## Main results

* `StarMemClass.instNormedStarGroup`: `NormedStarGroup` instance on star-closed additive subgroups.
* `TauCeti.closure_inter_selfAdjoint_inter_closedBall`: the closure of the self-adjoint elements
  of norm at most `r` of a star-closed submodule is the set of self-adjoint elements of norm at
  most `r` of its closure.
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

namespace TauCeti

open Metric

variable {𝕜 A S : Type*} [RCLike 𝕜] [NormedAddCommGroup A] [StarAddMonoid A] [NormedSpace 𝕜 A]
  [StarModule 𝕜 A] [ContinuousStar A] [SetLike S A] [AddSubmonoidClass S A]
  [SMulMemClass S 𝕜 A] [StarMemClass S A]

variable (𝕜) in
include 𝕜 in
/-- The closure of the self-adjoint elements of norm at most `r` of a star-closed `𝕜`-submodule
`s` is the set of self-adjoint elements of norm at most `r` of the closure of `s`. -/
theorem closure_inter_selfAdjoint_inter_closedBall (s : S) (r : ℝ) :
    closure ((s : Set A) ∩ selfAdjoint A ∩ closedBall 0 r) =
      closure (s : Set A) ∩ selfAdjoint A ∩ closedBall 0 r := by
  refine subset_antisymm ((closure_inter_subset_inter_closure _ _).trans
    (Set.inter_subset_inter ((closure_inter_subset_inter_closure _ _).trans
      (Set.inter_subset_inter_right _ (isClosed_eq continuous_star continuous_id).closure_subset))
      isClosed_closedBall.closure_subset)) ?_
  rintro y ⟨⟨hys, hysa⟩, hyr⟩
  have hyr' : ‖y‖ ≤ r := mem_closedBall_zero_iff.mp hyr
  rcases ((norm_nonneg y).trans hyr').eq_or_lt with rfl | hr
  · obtain rfl : y = 0 := norm_le_zero_iff.mp hyr'
    exact subset_closure ⟨⟨zero_mem s, .zero _⟩, mem_closedBall_self le_rfl⟩
  -- Take the real part, then rescale it into the ball.
  let re : A → A := fun x => (2⁻¹ : 𝕜) • (x + star x)
  let c : A → ℝ := fun x => r / max r ‖re x‖
  let f : A → A := fun x => (c x : 𝕜) • re x
  have hc : ∀ x, 0 < max r ‖re x‖ := fun x => hr.trans_le (le_max_left _ _)
  have hre : Continuous re := by fun_prop
  have hf : Continuous f :=
    (RCLike.continuous_ofReal.comp (continuous_const.div
      (continuous_const.max (continuous_norm.comp hre)) fun x => (hc x).ne')).smul hre
  have hfy : f y = y := by
    have hrey : re y = y := by
      simp only [re]
      rw [hysa.star_eq, ← two_smul 𝕜 y, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
    simp only [f, c, hrey, max_eq_left hyr', div_self hr.ne', RCLike.ofReal_one, one_smul]
  have hmaps : Set.MapsTo f s ((s : Set A) ∩ selfAdjoint A ∩ closedBall 0 r) := by
    intro x hx
    have h2 : IsSelfAdjoint (2⁻¹ : 𝕜) := by simp [IsSelfAdjoint]
    have hsa : IsSelfAdjoint (re x) := h2.smul (.add_star_self x)
    have hcx : IsSelfAdjoint (c x : 𝕜) := by simp [IsSelfAdjoint]
    refine ⟨⟨SMulMemClass.smul_mem _ (SMulMemClass.smul_mem _ (add_mem hx (star_mem hx))),
      hcx.smul hsa⟩, ?_⟩
    rw [mem_closedBall_zero_iff, norm_smul, RCLike.norm_ofReal, abs_of_pos (div_pos hr (hc x)),
      div_mul_eq_mul_div, div_le_iff₀ (hc x)]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hr.le
  exact hfy ▸ map_mem_closure hf hys hmaps

end TauCeti

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
