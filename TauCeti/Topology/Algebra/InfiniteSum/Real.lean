/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Unbounded weights preserving summability

A summable real sequence `a` remains summable after multiplication by suitable weights
`c n ≥ 1` tending to infinity: no summable sequence decays at a slowest possible rate. This is
the standard device for rescaling an absolutely convergent series of products `x n * y n` so that
one factor tends to zero while the other stays absolutely summable.

The weights count the blocks into which the tails of `|a|` are cut: `c n` is one more than the
number of indices `k` with `N k ≤ n`, where the tail of `|a|` beyond `N k` is at most `2⁻ᵏ`.

## Main results

* `Summable.exists_tendsto_atTop_summable_mul`: weights `c n ≥ 1` with `c n → ∞` and
  `∑ n, c n * a n` summable.
-/

public section

open Filter Finset
open scoped Topology

/-- A summable real sequence remains summable after multiplication by suitable weights `c n ≥ 1`
tending to infinity. -/
theorem Summable.exists_tendsto_atTop_summable_mul {a : ℕ → ℝ} (ha : Summable a) :
    ∃ c : ℕ → ℝ, (∀ n, 1 ≤ c n) ∧ Tendsto c atTop atTop ∧ Summable fun n ↦ c n * a n := by
  set b : ℕ → ℝ := fun n ↦ |a n| with hb_def
  have hb : Summable b := ha.abs
  have hb0 (n : ℕ) : 0 ≤ b n := abs_nonneg _
  -- A strictly increasing sequence of cut points `N k` beyond which the tail of `b` is `≤ 2⁻ᵏ`.
  obtain ⟨N, hN, hNtail⟩ : ∃ N : ℕ → ℕ, StrictMono N ∧
      ∀ k, ∑' m, b (m + N k) ≤ (1 / 2 : ℝ) ^ k :=
    extraction_forall_of_eventually fun k ↦
      (tendsto_sum_nat_add b).eventually (Iic_mem_nhds (by positivity))
  -- `d k` is `b` cut off below `N k`.
  set d : ℕ → ℕ → ℝ := fun k n ↦ if N k ≤ n then b n else 0 with hd_def
  have hd0 (k n : ℕ) : 0 ≤ d k n := by
    simp only [hd_def]
    split_ifs <;> simp [hb0]
  have hdk (k : ℕ) : Summable (d k) :=
    hb.of_nonneg_of_le (hd0 k) fun n ↦ by simp only [hd_def]; split_ifs <;> simp [hb0]
  have htsum_d (k : ℕ) : ∑' n, d k n ≤ (1 / 2 : ℝ) ^ k := by
    rw [← (hdk k).sum_add_tsum_nat_add (N k), Finset.sum_eq_zero fun i hi ↦ by
      simp [hd_def, not_le.2 (Finset.mem_range.1 hi)]]
    simpa [hd_def] using hNtail k
  -- Summing `d k n` over `k` first, then over `n`, is possible.
  have hprod : Summable fun p : ℕ × ℕ ↦ d p.1 p.2 :=
    (summable_prod_of_nonneg fun p ↦ hd0 p.1 p.2).2 ⟨hdk, (summable_geometric_two).of_nonneg_of_le
      (fun k ↦ tsum_nonneg (hd0 k)) htsum_d⟩
  have hcol : Summable fun n ↦ ∑' k, d k n :=
    ((summable_prod_of_nonneg fun p : ℕ × ℕ ↦ hd0 p.2 p.1).1
      ((Equiv.prodComm ℕ ℕ).summable_iff.2 hprod)).2
  -- Only the indices `k ≤ n` contribute to the column `n`, since `k ≤ N k`.
  have hcol_eq (n : ℕ) : ∑' k, d k n = ∑ k ∈ range (n + 1), d k n :=
    tsum_eq_sum fun k hk ↦ by
      have hk' : n + 1 ≤ k := by simpa using hk
      have hNk : k ≤ N k := hN.id_le k
      simp [hd_def, show ¬N k ≤ n by omega]
  -- The weight `c n` is one more than the number of cut points `N k ≤ n`.
  set c : ℕ → ℝ := fun n ↦ 1 + ∑ k ∈ range (n + 1), if N k ≤ n then (1 : ℝ) else 0 with hc_def
  have hc1 (n : ℕ) : 1 ≤ c n := by
    have : 0 ≤ ∑ k ∈ range (n + 1), if N k ≤ n then (1 : ℝ) else 0 :=
      Finset.sum_nonneg fun k _ ↦ by split_ifs <;> norm_num
    simp only [hc_def]
    linarith
  refine ⟨c, hc1, ?_, ?_⟩
  · refine tendsto_atTop_atTop.2 fun r ↦ ⟨N ⌈r⌉₊, fun n hn ↦ ?_⟩
    have hsub : range (⌈r⌉₊ + 1) ⊆ range (n + 1) :=
      Finset.range_subset_range.2 (Nat.succ_le_succ ((hN.id_le _).trans hn))
    have hones : ∑ k ∈ range (⌈r⌉₊ + 1), (if N k ≤ n then (1 : ℝ) else 0) = ⌈r⌉₊ + 1 := by
      rw [Finset.sum_ite_of_true fun k hk ↦
        (hN.monotone (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).trans hn]
      simp
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun k ↦ if N k ≤ n then (1 : ℝ) else 0) fun k _ _ ↦ by split_ifs <;> norm_num
    rw [hones] at hle
    simp only [hc_def]
    linarith [Nat.le_ceil r]
  · -- `|c n * a n| = b n + ∑ k ≤ n, d k n`, which is summable.
    refine summable_abs_iff.1 ((hb.add hcol).of_nonneg_of_le (fun n ↦ abs_nonneg _) fun n ↦ ?_)
    rw [abs_mul, abs_of_nonneg (zero_le_one.trans (hc1 n)), hcol_eq]
    simp only [hc_def, add_mul, one_mul, Finset.sum_mul]
    gcongr with k
    simp only [hd_def, hb_def]
    split_ifs <;> simp
