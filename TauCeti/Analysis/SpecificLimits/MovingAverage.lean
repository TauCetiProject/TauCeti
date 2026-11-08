/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Pointwise limits from moving averages

If every fixed time shift of a sequence is asymptotically indistinguishable from the
original sequence, then each fixed-length forward average is also asymptotically
indistinguishable from it. Consequently, uniform control of the forward averages implies
pointwise convergence. For nonnegative real sequences it suffices to bound the averages
above by a sequence tending to zero.

The one-sided criterion is the analytic step used to pass from uniform occupation bounds
to decay of transition probabilities in the null-recurrent case. No boundedness of the
original sequence is required. The averages include times `n + 1` through `n + k`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.8.
-/

public section

open Filter Finset Topology

namespace TauCeti

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- A fixed positive-length forward average differs negligibly from the original sequence
when every fixed shift does. -/
theorem tendsto_inv_smul_sum_range_add_sub {u : ℕ → E}
    (hshift : ∀ i, Tendsto (fun n => u (n + i) - u n) atTop (𝓝 0))
    {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun n => (k : ℝ)⁻¹ • ∑ i ∈ range k, u (n + i + 1) - u n)
      atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => ∑ i ∈ range k, (u (n + i + 1) - u n))
      atTop (𝓝 0) := by
    simpa [Nat.add_assoc] using tendsto_finsetSum (range k) (fun i _ => hshift (i + 1))
  convert hsum.const_smul (k : ℝ)⁻¹ using 1
  · funext n
    simp only [sum_sub_distrib, sum_const, card_range, smul_sub]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hk), one_smul]
  · simp

/-- Uniform bounds tending to zero on the distance of forward averages from `l` force
convergence to `l`, provided every fixed shift differs negligibly from the sequence. -/
theorem tendsto_of_norm_inv_smul_sum_range_add_sub_le {u : ℕ → E} {l : E} {b : ℕ → ℝ}
    (hshift : ∀ i, Tendsto (fun n => u (n + i) - u n) atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ (n k : ℕ), 0 < k →
      ‖(k : ℝ)⁻¹ • ∑ i ∈ range k, u (n + i + 1) - l‖ ≤ b k) :
    Tendsto u atTop (𝓝 l) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk, hbk⟩ : ∃ k, 0 < k ∧ b k < ε / 2 := by
    have hbε := hb.eventually (gt_mem_nhds (half_pos hε))
    obtain ⟨k, hk, hbk⟩ := ((eventually_gt_atTop 0).and hbε).exists
    exact ⟨k, hk, hbk⟩
  have havg := tendsto_inv_smul_sum_range_add_sub hshift hk.ne'
  have hnorm : Tendsto (fun n =>
      ‖(k : ℝ)⁻¹ • ∑ i ∈ range k, u (n + i + 1) - u n‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using havg.norm
  have hsmall := hnorm.eventually (gt_mem_nhds (half_pos hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have htriangle := dist_triangle (u n)
    ((k : ℝ)⁻¹ • ∑ i ∈ range k, u (n + i + 1)) l
  simp only [dist_eq_norm] at htriangle
  rw [norm_sub_rev (u n) ((k : ℝ)⁻¹ • ∑ i ∈ range k, u (n + i + 1))] at htriangle
  have := hN n hn
  have := hbound n k hk
  linarith

/-- A nonnegative real sequence tends to zero if fixed shifts differ negligibly and its
forward averages have a uniform upper bound tending to zero. The upper bound is needed
only for positive window lengths. -/
theorem tendsto_zero_of_nonneg_of_sum_range_add_div_le {u b : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n)
    (hshift : ∀ i, Tendsto (fun n => u (n + i) - u n) atTop (𝓝 0))
    (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ (n k : ℕ), 0 < k →
      (∑ i ∈ range k, u (n + i + 1)) / (k : ℝ) ≤ b k) :
    Tendsto u atTop (𝓝 0) := by
  refine tendsto_of_norm_inv_smul_sum_range_add_sub_le hshift hb fun n k hk => ?_
  have hnonneg : 0 ≤ (k : ℝ)⁻¹ * ∑ i ∈ range k, u (n + i + 1) :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k)) (sum_nonneg fun i _ => hu _)
  simp only [sub_zero, Real.norm_eq_abs, smul_eq_mul, abs_of_nonneg hnonneg]
  simpa only [div_eq_mul_inv, mul_comm] using hbound n k hk

end TauCeti
