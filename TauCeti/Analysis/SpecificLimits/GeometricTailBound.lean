/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Series bounds with a geometric tail

A bound on a finite prefix with one exceptional term can be combined with a geometric bound
on the remaining terms. Keeping the prefix and tail estimates separate is useful when only
one term in the prefix can be large.
-/

public section

open Finset
open scoped NNReal

namespace TauCeti

/-- A nonnegative series whose terms are at most `B * q^n` from index `N` onwards has sum at
most `N * w + C + B * q^N / (1 - q)` if each earlier term is at most `w`, with an extra
allowance `C` at index `j`. The exceptional index need not lie in the prefix. -/
theorem tsum_le_of_geometric_tail {f : ℕ → ℝ} {q : ℝ≥0} {B w C : ℝ} {N j : ℕ}
    (hq : (q : ℝ) < 1) (hC : 0 ≤ C) (hf : ∀ n, 0 ≤ f n)
    (hshort : ∀ n < N, f n ≤ w + if n = j then C else 0)
    (htail : ∀ n ≥ N, f n ≤ B * (q : ℝ) ^ n) :
    ∑' n, f n ≤ N * w + C + B * (q : ℝ) ^ N / (1 - q) := by
  have hg := (summable_geometric_of_lt_one q.coe_nonneg hq).mul_left (B * (q : ℝ) ^ N)
  have hshift (n : ℕ) : B * (q : ℝ) ^ (n + N) = (B * (q : ℝ) ^ N) * (q : ℝ) ^ n := by
    rw [pow_add, mul_comm ((q : ℝ) ^ n), mul_assoc]
  have htail' (n : ℕ) : f (n + N) ≤ (B * (q : ℝ) ^ N) * (q : ℝ) ^ n :=
    (htail _ (Nat.le_add_left N n)).trans_eq (hshift n)
  have hs := hg.of_nonneg_of_le (fun n ↦ hf (n + N)) htail'
  have hsum := (summable_nat_add_iff N).mp hs
  rw [← hsum.sum_add_tsum_nat_add N]
  refine add_le_add ?_ ((hs.tsum_le_tsum htail' hg).trans_eq ?_)
  · calc
      _ ≤ ∑ n ∈ range N, (w + if n = j then C else 0) :=
        sum_le_sum fun n hn ↦ hshort n (mem_range.mp hn)
      _ ≤ N * w + C := by
        simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_ite_eq', mem_range]
        split_ifs <;> linarith
  · rw [tsum_mul_left, tsum_geometric_of_lt_one q.coe_nonneg hq, div_eq_mul_inv]

end TauCeti
