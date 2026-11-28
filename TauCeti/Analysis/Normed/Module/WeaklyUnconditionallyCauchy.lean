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

The proof combines the following results. A non-summable family in a Banach space has pairwise
disjoint finite blocks with sums of norm bounded below
(`TauCeti.exists_pairwise_disjoint_le_norm_sum_of_not_cauchySeq`). These block sums again have
bounded finite subsums, so they are absolutely summable against every continuous linear functional
(`TauCeti.summable_norm_apply_of_forall_norm_sum_le`): they are weakly null but not norm null. A
basic subsequence of them (`TauCeti.exists_strictMono_norm_sum_range_le_two_mul`) therefore has
closed linear span isomorphic to `c₀`, through the bounded operator
`ZeroAtInftyContinuousMap.linearCombinationOfBddSums` out of `C₀(ℕ, 𝕜)`, which is bounded below.

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

/-- Let `v` be a sequence with bounded finite subsums, so that its linear combination map
`C₀(ℕ, 𝕜) →L[𝕜] X` is defined. If `v` is moreover a basic sequence with constant `2` whose terms
have norm at least `ε > 0`, then this map is bounded below: it is antilipschitz with constant
`4 / ε`. -/
private theorem exists_antilipschitzWith_linearCombinationOfBddSums [CompleteSpace X]
    {v : ℕ → X} (hv : ∃ C, ∀ s : Finset ℕ, ‖∑ i ∈ s, v i‖ ≤ C) {ε : ℝ} (hε : 0 < ε)
    (hvε : ∀ j, ε ≤ ‖v j‖) (hbasic : ∀ (a : ℕ → 𝕜) {m n : ℕ}, m ≤ n →
      ‖∑ i ∈ range m, a i • v i‖ ≤ 2 * ‖∑ i ∈ range n, a i • v i‖) :
    ∃ K, AntilipschitzWith K (ZeroAtInftyContinuousMap.linearCombinationOfBddSums 𝕜 v hv) := by
  set T := ZeroAtInftyContinuousMap.linearCombinationOfBddSums 𝕜 v hv
  -- Each coefficient is controlled by the partial sums, and these converge to `T a`.
  have hcoef (a : C₀(ℕ, 𝕜)) (m : ℕ) : ‖a m‖ * ε ≤ 4 * ‖T a‖ := by
    have hlim :=
      (ZeroAtInftyContinuousMap.hasSum_linearCombinationOfBddSums hv a).tendsto_sum_nat.norm
    refine ge_of_tendsto (hlim.const_mul 4) (eventually_atTop.2 ⟨m + 1, fun n hn ↦ ?_⟩)
    calc ‖a m‖ * ε ≤ ‖a m • v m‖ := by rw [norm_smul]; gcongr; exact hvε m
      _ = ‖∑ i ∈ range (m + 1), a i • v i - ∑ i ∈ range m, a i • v i‖ := by
          rw [sum_range_succ_sub_sum]
      _ ≤ ‖∑ i ∈ range (m + 1), a i • v i‖ + ‖∑ i ∈ range m, a i • v i‖ := norm_sub_le _ _
      _ ≤ 2 * ‖∑ i ∈ range n, a i • v i‖ + 2 * ‖∑ i ∈ range n, a i • v i‖ :=
          add_le_add (hbasic a hn) (hbasic a (by omega))
      _ = 4 * ‖∑ i ∈ range n, a i • v i‖ := by ring
  refine ⟨(4 / ε).toNNReal, T.antilipschitz_of_bound fun a ↦ ?_⟩
  rw [Real.coe_toNNReal _ (by positivity)]
  refine (ZeroAtInftyContinuousMap.norm_le (by positivity)).2 fun m ↦ ?_
  rw [div_mul_eq_mul_div, le_div_iff₀ hε]
  linarith [hcoef a m]

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
    exists_strictMono_norm_sum_range_le_two_mul hweak hε (Frequently.of_forall htε)
  have hv (s : Finset ℕ) : ‖∑ j ∈ s, u (φ j)‖ ≤ C := by
    rw [← sum_image hφ.injective.injOn]
    exact hu _
  obtain ⟨K, hK⟩ := exists_antilipschitzWith_linearCombinationOfBddSums ⟨C, hv⟩ hε hφε hbasic
  exact hX _ K hK

/-- **The `c₀` criterion for unconditional convergence.** A real or complex Banach space contains no
copy of `c₀`, that is admits no bounded-below continuous linear map from `C₀(ℕ, 𝕜)`, exactly when
every series in it with uniformly bounded finite subsums converges unconditionally. -/
theorem forall_summable_of_bounded_subsums_iff_forall_not_antilipschitzWith [CompleteSpace X] :
    (∀ x : ℕ → X, (∃ C, ∀ s : Finset ℕ, ‖∑ n ∈ s, x n‖ ≤ C) → Summable x) ↔
      ∀ (T : C₀(ℕ, 𝕜) →L[𝕜] X) (K : ℝ≥0), ¬AntilipschitzWith K T := by
  classical
  refine ⟨fun h T K hK ↦ ?_, fun hX x hx ↦ summable_of_forall_not_antilipschitzWith hX hx⟩
  -- The images of the coordinate vectors have bounded subsums but are not norm null.
  have hbound (s : Finset ℕ) : ‖∑ n ∈ s, ZeroAtInftyContinuousMap.single n (1 : 𝕜)‖ ≤ 1 := by
    rw [← coe_nnNorm, ← NNReal.coe_one, NNReal.coe_le_coe,
      ZeroAtInftyContinuousMap.nnnorm_sum_single]
    exact Finset.sup_le fun _ _ ↦ nnNorm_one.le
  have hsum := h (fun n ↦ T (ZeroAtInftyContinuousMap.single n 1)) ⟨‖T‖, fun s ↦ by
    rw [← map_sum]
    exact T.le_of_opNorm_le_of_le le_rfl (hbound s) |>.trans_eq (mul_one _)⟩
  have h0 := (tendsto_zero_iff_norm_tendsto_zero.1 hsum.tendsto_atTop_zero).const_mul (K : ℝ)
  rw [mul_zero] at h0
  obtain ⟨n, hn⟩ := (h0.eventually (gt_mem_nhds zero_lt_one)).exists
  have := hK.le_mul_norm (map_zero T) (ZeroAtInftyContinuousMap.single n (1 : 𝕜))
  rw [ZeroAtInftyContinuousMap.norm_single, norm_one] at this
  linarith

end TauCeti
