/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Changing endpoints in weighted quadratic sums

The difference between right- and left-endpoint weighted quadratic sums is bounded by
the largest weight increment times the unweighted quadratic sum. For continuous weights
on a compact time interval, the largest increment tends to zero as the mesh does.
Consequently changing endpoints does not affect a finite quadratic-sum limit.

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
theorem abs_sum_right_mul_sq_sub_sum_left_le {n : ℕ} (X B : Fin (n + 1) → ℝ) :
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

namespace ContinuousOn

variable {ι : Type*} {l : Filter ι} {N : ι → ℕ}
  {grid : ∀ k, Fin (N k + 1) → ℝ≥0} {a T : ℝ≥0} {δ : ι → ℝ}

/-- The largest increment of a continuous function on a compact horizon tends to zero
along arbitrary nondecreasing vanishing-mesh grids inside that horizon. -/
theorem tendsto_norm_partition_sub {E : Type*} [NormedAddCommGroup E]
    {X : ℝ≥0 → E} (hX : ContinuousOn X (Icc a T))
    (hgrid : ∀ k, Monotone (grid k)) (ha : ∀ k, a ≤ grid k 0)
    (hT : ∀ k, grid k (Fin.last (N k)) ≤ T)
    (hmesh : ∀ k (i : Fin (N k)), (grid k i.succ : ℝ) - grid k i.castSucc ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k ↦ ‖fun i : Fin (N k) ↦ X (grid k i.succ) - X (grid k i.castSucc)‖)
      l (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨η, hη, hclose⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hX) (ε / 2) (half_pos hε)
  filter_upwards [hδ.eventually_lt_const hη] with k hk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  refine (pi_norm_le_iff_of_nonneg (half_pos hε).le).2 (fun i ↦ ?_) |>.trans_lt (half_lt_self hε)
  have hmem (j : Fin (N k + 1)) : grid k j ∈ Icc a T :=
    ⟨(ha k).trans (hgrid k (Fin.zero_le j)), (hgrid k (Fin.le_last j)).trans (hT k)⟩
  have hd : dist (grid k i.succ) (grid k i.castSucc) < η := by
    rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (by
      exact_mod_cast (hgrid k (Fin.castSucc_le_succ i))))]
    exact (hmesh k i).trans_lt hk
  have hdist := hclose (grid k i.succ) (hmem _) (grid k i.castSucc) (hmem _) hd
  simpa only [dist_eq_norm] using hdist.le

/-- For continuous weights, changing from left to right endpoints preserves any finite
pathwise quadratic-sum limit. No path regularity of the integrator is required. -/
theorem tendsto_sum_right_mul_sq_sub_sum_left {X B : ℝ≥0 → ℝ}
    (hX : ContinuousOn X (Icc a T))
    (hgrid : ∀ k, Monotone (grid k)) (ha : ∀ k, a ≤ grid k 0)
    (hT : ∀ k, grid k (Fin.last (N k)) ≤ T)
    (hmesh : ∀ k (i : Fin (N k)), (grid k i.succ : ℝ) - grid k i.castSucc ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) {q : ℝ}
    (hQ : Tendsto (fun k ↦ ∑ i : Fin (N k),
      (B (grid k i.succ) - B (grid k i.castSucc)) ^ 2) l (𝓝 q)) :
    Tendsto (fun k ↦ (∑ i : Fin (N k), X (grid k i.succ) *
      (B (grid k i.succ) - B (grid k i.castSucc)) ^ 2) -
      ∑ i : Fin (N k), X (grid k i.castSucc) *
        (B (grid k i.succ) - B (grid k i.castSucc)) ^ 2) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  simp only [Real.norm_eq_abs]
  have hprod := (hX.tendsto_norm_partition_sub hgrid ha hT hmesh hδ).mul hQ
  rw [zero_mul] at hprod
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hprod
    (fun _ ↦ abs_nonneg _) (fun k ↦
      TauCeti.abs_sum_right_mul_sq_sub_sum_left_le (X ∘ grid k) (B ∘ grid k))

end ContinuousOn
