/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.PartitionOfUnity

/-!
# Approximation by partitions of unity adapted to a dense set

A compactly supported continuous function `f` with values in a pseudometric space with a
distinguished zero (for instance a normed space) admits, for every
`δ > 0` and every dense set `S` of the target, a finite partition of unity over the support of
`f` whose members have compact support, lie inside a prescribed neighbourhood of the support, and
are supported where `f` is `δ`-close to the corresponding point of `S`. When the target is a real
normed space, `f` is consequently uniformly within `δ` of the corresponding combination of those
points.

## Main results

* `CompactlySupportedContinuousMap.exists_partitionOfUnity_dist_lt`: the adapted finite
  partition of unity.
* `PartitionOfUnity.norm_sub_sum_smul_le`: the uniform estimate for a partition of unity whose
  members are supported where `f` is `δ`-close to the corresponding vector.
-/

public section

open Set Metric
open scoped CompactlySupported

variable {X : Type*} [TopologicalSpace X]

/-- A partition of unity over the support of `f`, all of whose members are supported where `f`
is within `δ` of the corresponding vector, gives a sum of scalar multiples of those vectors
within `δ` of `f` everywhere. -/
theorem PartitionOfUnity.norm_sub_sum_smul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (f : X → E)
    (ρ : PartitionOfUnity ι X (tsupport f)) (c : ι → E) {δ : ℝ} (hδ : 0 ≤ δ)
    (hρ : ∀ i x, ρ i x ≠ 0 → ‖f x - c i‖ ≤ δ) (x : X) :
    ‖f x - ∑ i, ρ i x • c i‖ ≤ δ := by
  have hsum : ∑ i, ρ i x • f x = f x := by
    rw [← Finset.sum_smul]
    by_cases hx : x ∈ tsupport f
    · simpa only [finsum_eq_sum_of_fintype, one_smul] using
        congrArg (fun r : ℝ => r • f x) (ρ.sum_eq_one hx)
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have heq : f x - ∑ i, ρ i x • c i = ∑ i, ρ i x • (f x - c i) := by
    simp only [smul_sub, Finset.sum_sub_distrib, hsum]
  rw [heq]
  calc
    ‖∑ i, ρ i x • (f x - c i)‖ ≤ ∑ i, ‖ρ i x • (f x - c i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ρ i x * δ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : ρ i x = 0
      · simp [hi]
      · rw [norm_smul, Real.norm_of_nonneg (ρ.nonneg i x)]
        exact mul_le_mul_of_nonneg_left (hρ i x hi) (ρ.nonneg i x)
    _ ≤ δ := by
      rw [← Finset.sum_mul]
      exact mul_le_of_le_one_left hδ (by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_le_one x)

namespace CompactlySupportedContinuousMap

variable [LocallyCompactSpace X] [T2Space X] {E : Type*} [PseudoMetricSpace E] [Zero E]

/-- A compactly supported continuous function admits a partition of unity over its support,
finitely indexed by a subset of a dense set, whose members have compact support inside a given
neighbourhood of the support and are supported where `f` is `δ`-close to the index. Only a
pseudometric and a distinguished zero on the target are needed. -/
theorem exists_partitionOfUnity_dist_lt (f : C_c(X, E)) {S : Set E} (hS : Dense S)
    {K : Set X} (hfK : tsupport f ⊆ interior K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (s : Finset S) (ρ : PartitionOfUnity s X (tsupport f)),
      (∀ i, HasCompactSupport (ρ i)) ∧
        ∀ i x, ρ i x ≠ 0 → x ∈ interior K ∧ dist (f x) (i.val.val : E) < δ := by
  let U (a : S) := interior K ∩ f ⁻¹' ball (a : E) δ
  have hU (a : S) : IsOpen (U a) :=
    isOpen_interior.inter (isOpen_ball.preimage f.continuous)
  have hcover : tsupport f ⊆ ⋃ a : S, U a := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := hS.exists_dist_lt (f x) hδ
    exact mem_iUnion.2 ⟨⟨a, ha⟩, hfK hx, hax⟩
  obtain ⟨s, hs⟩ := f.hasCompactSupport.elim_finite_subcover U hU hcover
  obtain ⟨ρ, hρ, hρc⟩ := PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space
    f.hasCompactSupport (fun a : s => U a) (fun a => hU a)
    (locallyFinite_of_finite _) (fun x hx => by
      obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.1 (hs hx)
      exact mem_iUnion.2 ⟨⟨a, ha⟩, hxa⟩)
  refine ⟨s, ρ, hρc, fun i x hx => ?_⟩
  have hxU := (hρ i (subset_closure hx))
  exact ⟨hxU.1, by simpa only [mem_preimage, mem_ball] using hxU.2⟩

end CompactlySupportedContinuousMap
