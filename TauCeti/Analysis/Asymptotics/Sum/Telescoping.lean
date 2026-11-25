/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Partial sums asymptotic to a telescoping model

Let `G` be a sequence in a normed group whose norm tends to infinity, and suppose that `G` moves
outward at a bounded angle: `‖G (k + 1) - G k‖ ≤ M (‖G (k + 1)‖ - ‖G k‖)` for every `k`. If the
terms `S k` of a second sequence are asymptotic to the forward differences `G (k + 1) - G k`, then
the partial sums `∑_{k < n} S k` are `G n + o(G n)`.

This is a discrete Stolz–Cesàro theorem for vector-valued sequences. In the real case, a
sequence `G` of constant sign whose absolute value `|G|` is monotone satisfies the angle condition
with `M = 1`. In the complex case it allows models such as `G k = e^{c √k}` with `Re c > 0`, whose
differences rotate, so that the partial sums do not grow like the sums of the norms of their
terms.
-/

public section

open Asymptotics Filter Finset

namespace TauCeti

/-- **Discrete Stolz–Cesàro for a model moving outward at a bounded angle.** Suppose
`‖G n‖ → ∞` and `‖G (k + 1) - G k‖ ≤ M (‖G (k + 1)‖ - ‖G k‖)` for every `k`. If
`S k - (G (k + 1) - G k) = o(G (k + 1) - G k)`, then `∑_{k < n} S k - G n = o(G n)`. -/
theorem isLittleO_sum_range_sub {E : Type*} [NormedAddCommGroup E] {S G : ℕ → E} {M : ℝ}
    (hS : (fun k => S k - (G (k + 1) - G k)) =o[atTop] fun k => G (k + 1) - G k)
    (hG : ∀ k, ‖G (k + 1) - G k‖ ≤ M * (‖G (k + 1)‖ - ‖G k‖))
    (hGtop : Tendsto (fun k => ‖G k‖) atTop atTop) :
    (fun n => ∑ k ∈ range n, S k - G n) =o[atTop] G := by
  have hsum_le (n : ℕ) : ∑ k ∈ range n, ‖G (k + 1) - G k‖ ≤ M * (‖G n‖ - ‖G 0‖) := by
    calc ∑ k ∈ range n, ‖G (k + 1) - G k‖ ≤ ∑ k ∈ range n, M * (‖G (k + 1)‖ - ‖G k‖) :=
          sum_le_sum fun k _ => hG k
      _ = M * (‖G n‖ - ‖G 0‖) := by rw [← mul_sum, sum_range_sub fun k => ‖G k‖]
  have hnorm_le (n : ℕ) : ‖G n‖ - ‖G 0‖ ≤ ∑ k ∈ range n, ‖G (k + 1) - G k‖ := by
    have h := norm_sum_le (range n) fun k => G (k + 1) - G k
    rw [sum_range_sub] at h
    linarith [norm_sub_norm_le (G n) (G 0)]
  have hsum_top : Tendsto (fun n => ∑ k ∈ range n, ‖G (k + 1) - G k‖) atTop atTop :=
    tendsto_atTop_mono hnorm_le (tendsto_atTop_add_const_right _ (-‖G 0‖) hGtop)
  -- The errors sum to `o` of the total variation of `G`, which is `O(‖G n‖)`.
  have herr := hS.norm_right.sum_range (fun k => norm_nonneg _) hsum_top
  have hvar : (fun n => ∑ k ∈ range n, ‖G (k + 1) - G k‖) =O[atTop] G := by
    refine IsBigO.of_bound |M| ?_
    filter_upwards [hGtop.eventually_ge_atTop ‖G 0‖] with n hn
    rw [Real.norm_of_nonneg (sum_nonneg fun k _ => norm_nonneg _)]
    calc ∑ k ∈ range n, ‖G (k + 1) - G k‖ ≤ M * (‖G n‖ - ‖G 0‖) := hsum_le n
      _ ≤ |M| * (‖G n‖ - ‖G 0‖) := mul_le_mul_of_nonneg_right (le_abs_self M) (by linarith)
      _ ≤ |M| * ‖G n‖ := by gcongr; linarith [norm_nonneg (G 0)]
  have hconst : (fun _ : ℕ => G 0) =o[atTop] G := isLittleO_const_left.2 (Or.inr hGtop)
  refine ((herr.trans_isBigO hvar).sub hconst).congr' (Eventually.of_forall fun n => ?_)
    EventuallyEq.rfl
  simp only [sum_sub_distrib (f := S), sum_range_sub]
  abel

end TauCeti
