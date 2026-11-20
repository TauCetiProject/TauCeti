/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.UniformContinuity
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Changing endpoints in weighted quadratic sums

The difference between right- and left-endpoint weighted quadratic sums is bounded by
the largest weight increment times the unweighted quadratic sum. For uniformly continuous
weights, the largest increment tends to zero as the mesh does. If the unweighted quadratic
sums are eventually bounded, the difference between the weighted endpoint sums tends to
zero. Thus changing endpoints preserves any limit of the weighted sums under this bound.

The integrator need not be continuous or have bounded variation. In stochastic applications
its quadratic sums converge only in probability; the pathwise result can then be applied
along almost surely convergent subsequences. No adaptation of the weight is used here.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

open Finset Filter Set
open scoped NNReal Topology

namespace TauCeti

/-- Changing the endpoint of the weight costs at most its largest increment times the
unweighted quadratic sum. Empty grids and unordered samples are allowed. -/
theorem abs_sum_succ_mul_sq_sub_sum_castSucc_le {n : ℕ} (X B : Fin (n + 1) → ℝ) :
    |(∑ i : Fin n, X i.succ * (B i.succ - B i.castSucc) ^ 2) -
      ∑ i : Fin n, X i.castSucc * (B i.succ - B i.castSucc) ^ 2| ≤
      ‖fun i : Fin n ↦ X i.succ - X i.castSucc‖ *
        ∑ i : Fin n, (B i.succ - B i.castSucc) ^ 2 := by
  rw [← sum_sub_distrib, mul_sum]
  calc
    _ ≤ ∑ i : Fin n, |X i.succ * (B i.succ - B i.castSucc) ^ 2 -
        X i.castSucc * (B i.succ - B i.castSucc) ^ 2| := abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |X i.succ - X i.castSucc| * (B i.succ - B i.castSucc) ^ 2 := by
      congr 1
      ext i
      rw [← sub_mul, abs_mul, abs_sq]
    _ ≤ _ := sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right
      (by simpa only [Real.norm_eq_abs] using
        norm_le_pi_norm (fun j : Fin n ↦ X j.succ - X j.castSucc) i) (sq_nonneg _)

end TauCeti

namespace UniformContinuousOn

/-- For uniformly continuous weights on vanishing-mesh grids, eventual boundedness of
the unweighted quadratic sums makes the difference between right- and left-endpoint
weighted sums tend to zero. No path regularity of the integrator is required. -/
theorem tendsto_sum_succ_mul_sq_sub_sum_castSucc {α ι : Type*} [PseudoMetricSpace α]
    {s : Set α} {X B : α → ℝ} (hX : UniformContinuousOn X s)
    {l : Filter ι} {N : ι → ℕ} {grid : ∀ k, Fin (N k + 1) → α} {δ : ι → ℝ}
    (hmem : ∀ᶠ k in l, ∀ j, grid k j ∈ s)
    (hmesh : ∀ᶠ k in l, ∀ i : Fin (N k), dist (grid k i.succ) (grid k i.castSucc) ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0))
    (hQ : l.IsBoundedUnder (· ≤ ·) (fun k ↦ ∑ i : Fin (N k),
      (B (grid k i.succ) - B (grid k i.castSucc)) ^ 2)) :
    Tendsto (fun k ↦ (∑ i : Fin (N k), X (grid k i.succ) *
      (B (grid k i.succ) - B (grid k i.castSucc)) ^ 2) -
      ∑ i : Fin (N k), X (grid k i.castSucc) *
        (B (grid k i.succ) - B (grid k i.castSucc)) ^ 2) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  simp only [Real.norm_eq_abs]
  have hinc := hX.tendsto_norm_sub_of_dist_le
    (hmem.mono fun _ hk i ↦ hk i.castSucc) (hmem.mono fun _ hk i ↦ hk i.succ) hmesh hδ
  have hnonneg (k : ι) : 0 ≤ ∑ i : Fin (N k),
      (B (grid k i.succ) - B (grid k i.castSucc)) ^ 2 :=
    sum_nonneg fun _ _ ↦ sq_nonneg _
  have hnorm : l.IsBoundedUnder (· ≤ ·) (fun k ↦ ‖∑ i : Fin (N k),
      (B (grid k i.succ) - B (grid k i.castSucc)) ^ 2‖) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using hQ
  have hprod := hinc.zero_mul_isBoundedUnder_le hnorm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprod
    (fun _ ↦ abs_nonneg _) (fun k ↦
      TauCeti.abs_sum_succ_mul_sq_sub_sum_castSucc_le (X ∘ grid k) (B ∘ grid k))

end UniformContinuousOn
