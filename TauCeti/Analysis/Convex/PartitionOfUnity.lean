/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Uniform approximation by finite partitions of unity

A continuous map `F` from a compact normal space `X` to a real normed space is uniformly
approximated by the finite convex combinations `x ↦ ∑ᶠ k, ρ k x • F k` of its own values at
finitely many points, with weights given by a partition of unity `ρ` indexed by those points.
This reduces statements about the uniform norm on `C(X, E)` to statements about finitely many
values. It is used, for example, to pass from Grothendieck's inequality for matrices to bounded
bilinear forms on spaces of continuous functions.

For scalar-valued families this gives `ContinuousMap.exists_partitionOfUnity_norm_sum_smul_sub_le`,
a uniform approximation of finitely many functions in `C(X, 𝕜)` by combinations of the
partition functions, and `PartitionOfUnity.norm_sum_smul_le_one` bounds the uniform norm of such
combinations with coefficients of norm at most one.
-/

public section

open Set Metric

namespace ContinuousMap

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X] [NormalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous map on a compact normal space is uniformly within `ε > 0` of the convex
combinations of its values at the points of a finite set `s`, weighted by a partition of unity
indexed by `s`. -/
theorem exists_partitionOfUnity_dist_finsum_smul_le (F : C(X, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset X) (ρ : PartitionOfUnity s X),
      ∀ x, dist (∑ᶠ k, ρ k x • F k) (F x) ≤ ε := by
  -- Cover `X` by the open sets where `F` is within `ε` of its value at a point.
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun k : X ↦ F ⁻¹' ball (F k) ε)
    (fun k ↦ isOpen_ball.preimage F.continuous)
    (fun x _ ↦ mem_iUnion.2 ⟨x, mem_ball_self hε⟩)
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite isClosed_univ
    (fun k : s ↦ F ⁻¹' ball (F k) ε) (fun k ↦ isOpen_ball.preimage F.continuous)
    (locallyFinite_of_finite _) fun x hx ↦ by
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 (hs hx)
      exact mem_iUnion.2 ⟨⟨k, hk⟩, hxk⟩
  refine ⟨s, ρ, fun x ↦ ?_⟩
  rw [← mem_closedBall]
  refine ρ.finsum_smul_mem_convex (g := fun k _ ↦ F k) (mem_univ x) (fun k hk ↦ ?_)
    (convex_closedBall (F x) ε)
  have hx : x ∈ F ⁻¹' ball (F k) ε := hρ k (subset_closure hk)
  exact mem_closedBall_comm.1 (ball_subset_closedBall hx)

/-- A finite family in `C(X, 𝕜)` is uniformly within `δ > 0` of the combinations
`∑ k, f i k • ρ k` of its values at the points of a finite set, for a partition of unity `ρ`
indexed by those points. -/
theorem exists_partitionOfUnity_norm_sum_smul_sub_le {𝕜 ι : Type*} [RCLike 𝕜] [Finite ι]
    (f : ι → C(X, 𝕜)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (s : Finset X) (ρ : PartitionOfUnity s X), ∀ i,
      ‖∑ k : s, f i k • (⟨fun x ↦ (ρ k x : 𝕜), by fun_prop⟩ : C(X, 𝕜)) - f i‖ ≤ δ := by
  have := Fintype.ofFinite ι
  obtain ⟨s, ρ, hρ⟩ := (ContinuousMap.pi f).exists_partitionOfUnity_dist_finsum_smul_le hδ
  refine ⟨s, ρ, fun i ↦ (ContinuousMap.norm_le _ hδ.le).2 fun x ↦ ?_⟩
  have hx := (norm_le_pi_norm (∑ᶠ k, ρ k x • ContinuousMap.pi f k - ContinuousMap.pi f x) i).trans
    ((dist_eq_norm _ _).symm.trans_le (hρ x))
  simpa only [ContinuousMap.sub_apply, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
    ContinuousMap.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ContinuousMap.pi_eval,
    finsum_eq_sum_of_fintype, Pi.sub_apply, RCLike.real_smul_eq_coe_mul, mul_comm] using hx

end ContinuousMap

namespace PartitionOfUnity

variable {X 𝕜 κ : Type*} [TopologicalSpace X] [CompactSpace X] [RCLike 𝕜] [Fintype κ]

/-- For a finite partition of unity `ρ` and scalars `c k` of norm at most one, the continuous
function `∑ k, c k * ρ k` has uniform norm at most one. -/
theorem norm_sum_smul_le_one (ρ : PartitionOfUnity κ X) {c : κ → 𝕜} (hc : ∀ k, ‖c k‖ ≤ 1) :
    ‖∑ k, c k • (⟨fun x ↦ (ρ k x : 𝕜), by fun_prop⟩ : C(X, 𝕜))‖ ≤ 1 := by
  refine (ContinuousMap.norm_le _ zero_le_one).2 fun x ↦ ?_
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
    ContinuousMap.coe_mk, smul_eq_mul]
  calc ‖∑ k, c k * (ρ k x : 𝕜)‖ ≤ ∑ k, ‖c k * (ρ k x : 𝕜)‖ := norm_sum_le _ _
    _ ≤ ∑ k, ρ k x := Finset.sum_le_sum fun k _ ↦ by
        rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (ρ.nonneg k x)]
        exact mul_le_of_le_one_left (ρ.nonneg k x) (hc k)
    _ ≤ 1 := by simpa only [finsum_eq_sum_of_fintype] using ρ.sum_le_one x

end PartitionOfUnity
