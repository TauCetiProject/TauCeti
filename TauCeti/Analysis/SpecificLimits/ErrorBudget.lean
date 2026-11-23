/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Order.PositiveSequence

/-!
# Summable error budgets with decreasing tolerances

For countably many error functions tending to zero as a positive accuracy parameter tends
to zero, choose decreasing tolerances below arbitrary positive control bounds. Every further
pointwise reduction of those tolerances respects a prescribed weighted absolute-error budget.
No monotonicity of the error functions, or boundedness of the weights, is required.

The construction uses Mathlib's `posSumOfEncodable` to allocate the total budget.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

/-- Choose a strictly decreasing positive accuracy schedule below given controls so that all
further positive reductions have summable weighted absolute errors with total at most `E`.
The weights are arbitrary real numbers, and the error functions need only tend to zero from
the right; neither positivity nor monotonicity of those functions is required. -/
theorem exists_strictAnti_errorBudget {f : ℕ → ℝ → ℝ} {b : ℕ → ℝ} {E : ℝ}
    (hf : ∀ n, Tendsto (f n) (𝓝[>] 0) (𝓝 0)) (hb : ∀ n, 0 < b n)
    (hE : 0 < E) (w : ℕ → ℝ) :
    ∃ δ : ℕ → ℝ, StrictAnti δ ∧ (∀ n, 0 < δ n ∧ δ n < b n) ∧
      Tendsto δ atTop (𝓝 0) ∧
      ∀ d : ℕ → ℝ, (∀ n, 0 < d n ∧ d n ≤ δ n) →
        Summable (fun n ↦ |w n * f n (d n)|) ∧ ∑' n, |w n * f n (d n)| ≤ E := by
  obtain ⟨η, hη, c, hc, hcE⟩ := posSumOfEncodable hE ℕ
  have hsmall (n : ℕ) : ∃ a > (0 : ℝ), ∀ x ∈ Ioo 0 a, |w n * f n x| < η n := by
    have hlim : Tendsto (fun x ↦ |w n * f n x|) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul (hf n)).abs
    exact (nhdsGT_basis 0).mem_iff.mp (hlim.eventually (eventually_lt_nhds (hη n)))
  choose a ha hsmall using hsmall
  obtain ⟨δ, hanti, hδ, hlim⟩ := exists_strictAnti_pos_lt_tendsto_zero
    (fun n ↦ lt_min (hb n) (ha n))
  refine ⟨δ, hanti, fun n ↦ ⟨(hδ n).1, (hδ n).2.trans_le (min_le_left _ _)⟩,
    hlim, fun d hd ↦ ?_⟩
  have hbound : ∀ n, |w n * f n (d n)| ≤ η n := fun n ↦
    (hsmall n (d n) ⟨(hd n).1,
      (hd n).2.trans_lt ((hδ n).2.trans_le (min_le_right _ _))⟩).le
  have hsum := hc.summable.of_nonneg_of_le (fun n ↦ abs_nonneg _) hbound
  exact ⟨hsum, (hsum.tsum_le_tsum hbound hc.summable).trans (hc.tsum_eq.trans_le hcE)⟩

end TauCeti
