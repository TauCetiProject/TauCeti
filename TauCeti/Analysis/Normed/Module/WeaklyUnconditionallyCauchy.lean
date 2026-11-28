/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
import TauCeti.Analysis.Normed.Group.InfiniteSum
import TauCeti.Analysis.Normed.Module.Bases.WeaklyNull
import TauCeti.Analysis.Normed.Module.BoundedCoefficients
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.LinearCombination

/-!
# Series with bounded finite subsums and copies of `c₀`

A series `∑ xₙ` in a real or complex normed space is *weakly unconditionally Cauchy* when its
finite subsums `∑ n ∈ s, x n` are uniformly bounded; equivalently, its finite signed sums
`∑ n ∈ s, ± x n` are, since each signed sum is a difference of two subsums. Every unconditionally
convergent series has this property, and the unit vectors of `c₀` show that the converse fails.
This file proves that `c₀` is the only obstruction (Bessaga–Pełczyński):

* `TauCeti.summable_of_forall_not_antilipschitzWith`: if a Banach space `X` contains no copy of
  `c₀`, that is no bounded-below continuous linear map `C₀(ℕ, 𝕜) →L[𝕜] X`, then every family in
  `X` with bounded finite subsums is summable;
* `TauCeti.forall_summable_of_bounded_subsums_iff_forall_not_antilipschitzWith`: this property of
  sequences characterizes the Banach spaces containing no copy of `c₀`.

The proof combines the following results. Let `x` be a family in a Banach space whose finite
subsums are uniformly bounded but which is not summable. It has pairwise disjoint finite blocks
with sums of norm bounded below
(`TauCeti.exists_pairwise_disjoint_le_norm_sum_of_not_cauchySeq`). Since the blocks are disjoint,
the finite subsums of these block sums are finite subsums of `x`, hence uniformly bounded, so the
block sums are absolutely summable against every continuous linear functional
(`TauCeti.summable_norm_apply_of_forall_norm_sum_le`): they are weakly null but not norm null. A
basic subsequence of them (`TauCeti.exists_strictMono_norm_sum_range_le_mul`) therefore has
closed linear span isomorphic to `c₀`, through the bounded operator
`ZeroAtInftyContinuousMap.linearCombinationOfBoundedSubsums` out of `C₀(ℕ, 𝕜)`, which is bounded
below (`ZeroAtInftyContinuousMap.antilipschitzWith_linearCombinationOfBoundedSubsums`).

## References

* C. Bessaga and A. Pełczyński, *On bases and unconditional convergence of series in Banach
  spaces*, Studia Math. 17 (1958), 151–164.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Theorem 2.4.11.
* J. Diestel, *Sequences and Series in Banach Spaces*, Chapter V, Theorem 8.
-/

public section

open Filter Finset Function Topology
open scoped NNReal ZeroAtInfty

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

namespace TauCeti

/-- **Bessaga–Pełczyński.** In a real or complex Banach space containing no copy of `c₀`, that is
admitting no bounded-below continuous linear map from `C₀(ℕ, 𝕜)`, every family with uniformly
bounded finite subsums, indexed by any type, is summable. -/
theorem summable_of_forall_not_antilipschitzWith [CompleteSpace X]
    (hX : ∀ (T : C₀(ℕ, 𝕜) →L[𝕜] X) (K : ℝ≥0), ¬AntilipschitzWith K T) {ι : Type*} {x : ι → X}
    (hx : ∃ C, ∀ s : Finset ι, ‖∑ i ∈ s, x i‖ ≤ C) : Summable x := by
  classical
  by_contra hns
  obtain ⟨C, hC⟩ := hx
  obtain ⟨ε, hε, t, ht, htε⟩ := exists_pairwise_disjoint_le_norm_sum_of_not_cauchySeq
    fun h ↦ hns (summable_iff_cauchySeq_finset.2 h)
  -- The block sums `u k` have bounded subsums, so they are weakly null but not norm null.
  set u : ℕ → X := fun k ↦ ∑ i ∈ t k, x i
  have hu (s : Finset ℕ) : ‖∑ k ∈ s, u k‖ ≤ C := by
    rw [← sum_biUnion (ht.set_pairwise _)]
    exact hC _
  have hweak (f : StrongDual 𝕜 X) : Tendsto (fun k ↦ f (u k)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2
      (summable_norm_apply_of_forall_norm_sum_le hu f).tendsto_atTop_zero
  -- A basic subsequence of the block sums has closed linear span isomorphic to `c₀`.
  obtain ⟨φ, hφ, hφε, hbasic⟩ :=
    exists_strictMono_norm_sum_range_le_mul hweak hε (Frequently.of_forall htε) one_lt_two
  have hv (s : Finset ℕ) : ‖∑ j ∈ s, u (φ j)‖ ≤ C := by
    rw [← sum_image hφ.injective.injOn]
    exact hu _
  exact hX _ _ <|
    ZeroAtInftyContinuousMap.antilipschitzWith_linearCombinationOfBoundedSubsums ⟨C, hv⟩ hε hφε
      hbasic

/-- **The `c₀` criterion for unconditional convergence.** A real or complex Banach space contains no
copy of `c₀`, that is admits no bounded-below continuous linear map from `C₀(ℕ, 𝕜)`, exactly when
every series in it with uniformly bounded finite subsums converges unconditionally. -/
theorem forall_summable_of_bounded_subsums_iff_forall_not_antilipschitzWith [CompleteSpace X] :
    (∀ x : ℕ → X, (∃ C, ∀ s : Finset ℕ, ‖∑ n ∈ s, x n‖ ≤ C) → Summable x) ↔
      ∀ (T : C₀(ℕ, 𝕜) →L[𝕜] X) (K : ℝ≥0), ¬AntilipschitzWith K T := by
  classical
  refine ⟨fun h T K hK ↦ ?_, fun hX x hx ↦ summable_of_forall_not_antilipschitzWith hX hx⟩
  -- The images of the coordinate vectors have bounded subsums, so they tend to zero.
  have hsum := h (fun n ↦ T (ZeroAtInftyContinuousMap.single n 1))
    ⟨‖T‖, ZeroAtInftyContinuousMap.norm_sum_apply_single_one_le T⟩
  -- Pulling this back through the embedding `T`, the coordinate vectors would tend to zero.
  have h0 : Tendsto (fun n : ℕ ↦ ZeroAtInftyContinuousMap.single n (1 : 𝕜)) atTop (𝓝 0) := by
    rw [(hK.isInducing T.continuous).tendsto_nhds_iff, comp_def, map_zero]
    exact hsum.tendsto_atTop_zero
  obtain ⟨n, hn⟩ := (h0.norm.eventually (gt_mem_nhds (norm_zero.trans_lt zero_lt_one))).exists
  simp at hn

end TauCeti
