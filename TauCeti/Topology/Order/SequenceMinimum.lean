/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Attainment of a sequence minimum from a lower barrier

A sequence bounded below by a sequence converging to `c` attains its minimum if it
has values at most `c` arbitrarily far out. This allows a converging lower barrier
to certify attainment without requiring convergence of the sequence itself.
A real sequence tending to zero with a value greater than one has a last maximizing
index; this is useful in dominant-term arguments for ultrametric sums.
-/

public section

open Filter Set Finset
open scoped Topology

namespace Filter.Tendsto

/-- A sequence above a convergent lower barrier attains its minimum, with value at
most the barrier's limit, provided it has values at most that limit frequently. -/
theorem exists_minimum_of_lower_bound {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] {a b : ℕ → α} {c : α}
    (hb : Tendsto b atTop (𝓝 c)) (hba : ∀ n, b n ≤ a n)
    (ha : ∃ᶠ n in atTop, a n ≤ c) :
    ∃ n, a n ≤ c ∧ ∀ m, a n ≤ a m := by
  classical
  by_cases h : ∀ n, c ≤ a n
  · obtain ⟨n, hn⟩ := ha.exists
    exact ⟨n, hn, fun m => hn.trans (h m)⟩
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have htail : ∀ᶠ n in atTop, a i < a n :=
      (hb.eventually (eventually_gt_nhds hi)).mono fun n hn => hn.trans_le (hba n)
    obtain ⟨N, hN⟩ := eventually_atTop.1 htail
    obtain ⟨k, _, hmin⟩ := Set.exists_min_image (Set.Iic (max N i)) a (Set.finite_Iic _)
      ⟨i, le_max_right N i⟩
    refine ⟨k, (hmin i (le_max_right N i)).trans hi.le, fun m => ?_⟩
    by_cases hm : m ≤ max N i
    · exact hmin m hm
    · exact (hmin i (le_max_right N i)).trans (hN m (by omega)).le

/-- A real sequence tending to zero, initially at most one and then greater than one,
has a positive last maximizing index, whose value is greater than one. -/
theorem exists_last_max_of_tendsto_zero {t : ℕ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (ht0 : t 0 ≤ 1) (ht1 : 1 < t 1) :
    ∃ k : ℕ, 0 < k ∧ 1 < t k ∧ (∀ n, t n ≤ t k) ∧ ∀ n, k < n → t n < t k := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (zero_lt_one.trans ht1)))
  have h1N : 1 < N := by
    by_contra! h
    exact (hN 1 h).false
  obtain ⟨j, hj, hjmax⟩ := (range N).exists_max_image t ⟨1, mem_range.mpr h1N⟩
  have hj1 : 1 < t j := ht1.trans_le (hjmax 1 (mem_range.mpr h1N))
  let S := (range N).filter fun i ↦ t i = t j
  have hS : S.Nonempty := ⟨j, mem_filter.mpr ⟨hj, rfl⟩⟩
  let k := S.max' hS
  have hkS : k ∈ S := S.max'_mem hS
  have hk : t k = t j := (mem_filter.mp hkS).2
  have hmax (n : ℕ) : t n ≤ t k := by
    rw [hk]
    by_cases hn : n < N
    · exact hjmax n (mem_range.mpr hn)
    · exact (hN n (by omega)).le.trans (hjmax 1 (mem_range.mpr h1N))
  refine ⟨k, ?_, by rwa [hk], hmax, ?_⟩
  · by_contra! h
    have hk0 : k = 0 := by omega
    rw [hk0] at hk
    linarith
  · intro n hn
    refine (hmax n).lt_of_ne fun heq ↦ ?_
    have hnN : n < N := by
      by_contra! h
      have := hN n h
      linarith [hjmax 1 (mem_range.mpr h1N)]
    have hnS : n ∈ S := mem_filter.mpr ⟨mem_range.mpr hnN, heq.trans hk⟩
    exact (S.le_max' n hnS).not_gt hn

end Filter.Tendsto
