/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The unfinished interval in quadratic sums

A quadratic sum stopped at an observation time includes a partial increment in the
interval containing that time. The sum over completed intervals does not. Their difference
is nonnegative and consists of at most one squared distance. On vanishing-mesh grids,
continuity of the path makes this difference tend to zero uniformly on a compact horizon.

This is the pathwise interpolation step for upgrading maximal estimates at partition dates
to uniform-in-time quadratic-variation convergence. It requires no variation bound on the
path. The grids may have repeated dates or no intervals. The distance formulation also
applies to paths in arbitrary pseudometric spaces.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §1.5, for quadratic-variation sums and uniform convergence in probability.
-/

public section

open Finset Set Filter
open scoped NNReal Topology

namespace TauCeti

variable {E : Type*} [PseudoMetricSpace E] {n : ℕ}
  {τ : Fin (n + 1) → ℝ≥0} {u : ℝ≥0}

/-- The difference between the clipped quadratic sum and the sum over completed intervals
is exactly the contribution of the (at most one) interval strictly containing the observation
time. At grid dates that contribution is zero. -/
theorem sum_sq_dist_min_sub_completed (x : ℝ≥0 → E) (hτ : Monotone τ) :
    (∑ i : Fin n, dist (x (min u (τ i.succ))) (x (min u (τ i.castSucc))) ^ 2) -
        (∑ i : Fin n, if τ i.succ ≤ u then dist (x (τ i.succ)) (x (τ i.castSucc)) ^ 2
          else 0) =
      ∑ i ∈ univ.filter (fun i : Fin n ↦ τ i.castSucc < u ∧ u < τ i.succ),
        dist (x u) (x (τ i.castSucc)) ^ 2 := by
  rw [← sum_sub_distrib, sum_filter]
  refine sum_congr rfl fun i _ ↦ ?_
  have hi := hτ (Fin.castSucc_le_succ i)
  by_cases hr : τ i.succ ≤ u
  · simp [hr, min_eq_right (hi.trans hr), not_lt_of_ge hr]
  · by_cases hl : u ≤ τ i.castSucc
    · simp [hr, min_eq_left hl, min_eq_left (hl.trans hi), not_lt_of_ge hl]
    · simp [hr, lt_of_not_ge hr, lt_of_not_ge hl, min_eq_left (le_of_not_ge hr),
        min_eq_right (le_of_not_ge hl)]

/-- If the oscillation from the left endpoint to any point inside each grid cell is at most
`c`, the unfinished-interval contribution lies in `[0,c²]`, independently of the grid size. -/
theorem sum_sq_dist_min_sub_completed_mem_Icc (x : ℝ≥0 → E) (hτ : Monotone τ)
    {c : ℝ}
    (hosc : ∀ i : Fin n, τ i.castSucc < u → u < τ i.succ →
      dist (x u) (x (τ i.castSucc)) ≤ c) :
    (∑ i : Fin n, dist (x (min u (τ i.succ))) (x (min u (τ i.castSucc))) ^ 2) -
        (∑ i : Fin n, if τ i.succ ≤ u then dist (x (τ i.succ)) (x (τ i.castSucc)) ^ 2
          else 0) ∈ Icc 0 (c ^ 2) := by
  rw [sum_sq_dist_min_sub_completed x hτ]
  let s := univ.filter (fun i : Fin n ↦ τ i.castSucc < u ∧ u < τ i.succ)
  have hcard : s.card ≤ 1 := by
    refine card_le_one.2 fun i hi j hj ↦ ?_
    have hi := (mem_filter.1 hi).2
    have hj := (mem_filter.1 hj).2
    apply le_antisymm
    · by_contra h
      have hji : j.succ ≤ i.castSucc := by simpa using Nat.succ_le_of_lt (lt_of_not_ge h)
      exact (not_lt_of_ge (hτ hji)) (hi.1.trans hj.2)
    · by_contra h
      have hij : i.succ ≤ j.castSucc := by simpa using Nat.succ_le_of_lt (lt_of_not_ge h)
      exact (not_lt_of_ge (hτ hij)) (hj.1.trans hi.2)
  refine ⟨sum_nonneg (fun _ _ ↦ sq_nonneg _), ?_⟩
  calc
    _ ≤ (s.card : ℝ) * c ^ 2 := by
      simpa only [nsmul_eq_mul] using s.sum_le_card_nsmul
        (fun i ↦ dist (x u) (x (τ i.castSucc)) ^ 2) (c ^ 2) (fun i hi ↦ by
          have hi := (mem_filter.1 hi).2
          exact pow_le_pow_left₀ dist_nonneg (hosc i hi.1 hi.2) 2)
    _ ≤ c ^ 2 := by
      have : (s.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      nlinarith [sq_nonneg c]

end TauCeti

namespace ContinuousOn

variable {E : Type*} [PseudoMetricSpace E] {x : ℝ≥0 → E} {a b : ℝ≥0}

/-- For a continuous path on a compact horizon, the clipped quadratic sum and the sum over
completed intervals differ by a quantity tending uniformly to zero along every vanishing-mesh
family. No nesting, variation or moment assumption is needed. -/
theorem tendstoUniformlyOn_sum_sq_dist_min_sub_completed (hx : ContinuousOn x (Icc a b))
    {ι : Type*} {l : Filter ι} {N : ι → ℕ}
    {grid : ∀ k, Fin (N k + 1) → ℝ≥0} (hgrid : ∀ k, Monotone (grid k))
    (ha : ∀ k, grid k 0 = a) (hb : ∀ k, grid k (Fin.last (N k)) = b)
    {δ : ι → ℝ}
    (hmesh : ∀ k (i : Fin (N k)), dist (grid k i.succ) (grid k i.castSucc) ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    TendstoUniformlyOn (fun k u ↦
      (∑ i : Fin (N k),
        dist (x (min u (grid k i.succ))) (x (min u (grid k i.castSucc))) ^ 2) -
      (∑ i : Fin (N k), if grid k i.succ ≤ u then
        dist (x (grid k i.succ)) (x (grid k i.castSucc)) ^ 2 else 0))
      (fun _ ↦ 0) l (Icc a b) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let c := min ε 1 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hcε : c ^ 2 < ε := by
    have h₁ : c ≤ ε / 2 := by dsimp [c]; gcongr; exact min_le_left _ _
    have h₂ : c ≤ 1 / 2 := by dsimp [c]; gcongr; exact min_le_right _ _
    nlinarith
  obtain ⟨d, hd, hosc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hx) c hc
  filter_upwards [hδ.eventually_lt_const hd] with k hk
  intro u hu
  have hmem (j : Fin (N k + 1)) : grid k j ∈ Icc a b := by
    constructor
    · simpa only [ha k] using hgrid k (Fin.zero_le j)
    · simpa only [hb k] using hgrid k (Fin.le_last j)
  have hbound := TauCeti.sum_sq_dist_min_sub_completed_mem_Icc x (hgrid k)
    (u := u) (fun i hl hr ↦ by
      apply le_of_lt (hosc u hu (grid k i.castSucc) (hmem i.castSucc) ?_)
      calc
        dist u (grid k i.castSucc) ≤ dist (grid k i.succ) (grid k i.castSucc) := by
          have hl' : (grid k i.castSucc : ℝ) ≤ u := by exact_mod_cast hl.le
          have hr' : (u : ℝ) ≤ grid k i.succ := by exact_mod_cast hr.le
          have hi' : (grid k i.castSucc : ℝ) ≤ grid k i.succ := hl'.trans hr'
          simp only [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 hl'),
            abs_of_nonneg (sub_nonneg.2 hi')]
          exact sub_le_sub_right hr' _
        _ ≤ δ k := hmesh k i
        _ < d := hk)
  simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hbound.1] using
    hbound.2.trans_lt hcε

end ContinuousOn
