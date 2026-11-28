/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Cesàro means of antitone sequences in `ℝ≥0∞`

An antitone sequence `c : ℕ → ℝ≥0∞` with `c 0 ≠ ∞` converges to `⨅ k, c k`, and so do its
Cesàro means `(∑ k < n, c k) / n`.

## Main results

* `ENNReal.tendsto_sum_range_div_of_antitone`: the Cesàro means of an antitone sequence with
  finite first term tend to its infimum.
-/

public section

open Filter Finset Topology
open scoped ENNReal

namespace ENNReal

/-- The Cesàro means `(∑ k < n, c k) / n` of an antitone sequence `c` in `ℝ≥0∞` with `c 0 ≠ ∞`
tend to its infimum `⨅ k, c k`. -/
theorem tendsto_sum_range_div_of_antitone {c : ℕ → ℝ≥0∞} (hc : Antitone c) (h0 : c 0 ≠ ∞) :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ range n, c k) / n) atTop (𝓝 (⨅ k, c k)) := by
  refine tendsto_order.2 ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · -- Every term is at least the infimum, hence so is every mean of positive length.
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
    refine hb.trans_le ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl (natCast_ne_top n)), mul_comm]
    calc (n : ℝ≥0∞) * ⨅ k, c k = ∑ _k ∈ range n, ⨅ k, c k := by simp
      _ ≤ ∑ k ∈ range n, c k := sum_le_sum fun k _ ↦ iInf_le c k
  · -- For `c m < b`, split off the first `m` terms: the mean is at most `m * c 0 / n + c m`.
    obtain ⟨m, hm⟩ := iInf_lt_iff.1 hb
    have hbound : ∀ n, m ≤ n → 0 < n → (∑ k ∈ range n, c k) / n ≤ m * c 0 / n + c m :=
      fun n hmn hn ↦ by
        have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
        rw [ENNReal.div_le_iff hn0 (natCast_ne_top n), add_mul,
          ENNReal.div_mul_cancel hn0 (natCast_ne_top n), ← sum_range_add_sum_Ico _ hmn,
          mul_comm (c m)]
        gcongr
        · calc ∑ k ∈ range m, c k ≤ ∑ _k ∈ range m, c 0 :=
                sum_le_sum fun k _ ↦ hc (Nat.zero_le k)
            _ = m * c 0 := by simp
        · calc ∑ k ∈ Ico m n, c k ≤ ∑ _k ∈ Ico m n, c m :=
                sum_le_sum fun k hk ↦ hc (mem_Ico.mp hk).1
            _ = (n - m : ℕ) * c m := by simp
            _ ≤ n * c m := by gcongr; exact Nat.sub_le n m
    have htend : Tendsto (fun n : ℕ ↦ m * c 0 / n + c m) atTop (𝓝 (c m)) := by
      have h : Tendsto (fun n : ℕ ↦ m * c 0 / n) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
          (Or.inr (mul_ne_top (natCast_ne_top m) h0))
      simpa using h.add_const (c m)
    filter_upwards [htend.eventually (gt_mem_nhds hm), eventually_ge_atTop (m + 1)] with n h1 h2
    exact (hbound n (by omega) (by omega)).trans_lt h1

end ENNReal
