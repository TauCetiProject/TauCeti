/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Taylor.Basic

/-!
# Accumulated Taylor remainders

Second-order Taylor errors can be summed along finite grids without a bound on the number of
grid points. For a function C³ near a compact interval with bounded third derivative there,
the error is bounded by the largest increment times the sum of squared increments. For a C²
function, uniform continuity of the second derivative on a compact interval gives a vanishing
coefficient instead. Consequently, if the largest increment tends to zero and the quadratic
sums remain bounded, the accumulated remainder tends to zero. The grids may contain
repetitions or be empty.

These are deterministic estimates for the Taylor-expansion step in change-of-variables
formulas along paths with controlled quadratic sums. They do not assert convergence of the
first- or second-order sums separately.

The one-step expansion uses Mathlib's Taylor theorem with Lagrange remainder.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

/-- The endpoint increment minus the linear and quadratic Taylor sums is the sum of the
individual second-order Taylor remainders. No regularity or ordering of the grid is needed. -/
theorem sub_sum_taylor_two_eq_sum_sub_taylorWithinEval (f : ℝ → ℝ) (x : ℕ → ℝ) (n : ℕ) :
    f (x n) - f (x 0) -
      (∑ i ∈ Finset.range n, deriv f (x i) * (x (i + 1) - x i)) -
      1 / 2 * (∑ i ∈ Finset.range n,
        deriv (deriv f) (x i) * (x (i + 1) - x i) ^ 2) =
      ∑ i ∈ Finset.range n,
        (f (x (i + 1)) - taylorWithinEval f 2 univ (x i) (x (i + 1))) := by
  rw [← Finset.sum_range_sub (fun i ↦ f (x i)) n, ← Finset.sum_sub_distrib,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [taylorWithinEval_univ_two]
  ring

/-- A third-derivative bound on an interval containing the grid controls the accumulated
second-order Taylor remainder by the largest increment and the quadratic sum, independently
of the size of the finite grid. Only C³ regularity near that interval is required. -/
theorem abs_sum_sub_taylorWithinEval_two_le {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ z ∈ Icc a b, ContDiffAt ℝ 3 f z)
    {M δ : ℝ} (hM : ∀ z ∈ Icc a b, |iteratedDeriv 3 f z| ≤ M) (x : ℕ → ℝ) (n : ℕ)
    (hx : ∀ i ≤ n, x i ∈ Icc a b) (hδ : ∀ i < n, |x (i + 1) - x i| ≤ δ) :
    |∑ i ∈ Finset.range n, (f (x (i + 1)) - taylorWithinEval f 2 univ (x i) (x (i + 1)))| ≤
      M / 6 * δ * ∑ i ∈ Finset.range n, (x (i + 1) - x i) ^ 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM _ (hx 0 (Nat.zero_le n)))
  -- Apply the Lagrange remainder on each step, keeping its intermediate point in the interval.
  have hstep i (hi : i ∈ Finset.range n) :
      ‖f (x (i + 1)) - taylorWithinEval f 2 univ (x i) (x (i + 1))‖ ≤
        M / 6 * δ * (x (i + 1) - x i) ^ 2 := by
    rw [Real.norm_eq_abs]
    have hi' := Finset.mem_range.1 hi
    have hsub := uIcc_subset_Icc (hx i hi'.le) (hx (i + 1) hi')
    by_cases h : x i = x (i + 1)
    · simp [h]
    obtain ⟨z, hz, hTaylor⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (n := 2) h (fun t ht ↦ (hf t (hsub ht)).contDiffWithinAt)
    have htay : taylorWithinEval f 2 (uIcc (x i) (x (i + 1))) (x i) (x (i + 1)) =
        taylorWithinEval f 2 univ (x i) (x (i + 1)) := by
      simp only [taylor_within_apply]
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc h)
        ((hf _ (hx i hi'.le)).of_le (by norm_cast; simp at hj; omega)) left_mem_uIcc,
        iteratedDerivWithin_univ]
    rw [htay] at hTaylor
    calc
      _ = |iteratedDeriv 3 f z| * |x (i + 1) - x i| ^ 3 / 6 := by
        rw [hTaylor, abs_div, abs_mul, abs_pow]
        norm_num
      _ ≤ M * |x (i + 1) - x i| ^ 3 / 6 := by
        gcongr
        exact hM z (hsub (uIoo_subset_uIcc_self hz))
      _ = |x (i + 1) - x i| * (M / 6 * (x (i + 1) - x i) ^ 2) := by
        rw [pow_succ, sq_abs]
        ring
      _ ≤ δ * (M / 6 * (x (i + 1) - x i) ^ 2) :=
        mul_le_mul_of_nonneg_right (hδ i hi') (by positivity)
      _ = _ := by ring
  -- Mathlib's finite-sum bound combines the per-step quadratic estimates.
  simpa only [Real.norm_eq_abs, ← Finset.mul_sum] using
    norm_sum_le_of_le (Finset.range n) hstep

/-- The sum of the first- and second-order Taylor terms approximates the endpoint increment
for functions C² near a fixed compact interval and grids eventually confined to it, with
vanishing increments and eventually bounded quadratic sums. The grid family may be indexed
by any filter. No nesting, ordering, or bound on the number of grid points is required. -/
theorem tendsto_sub_sum_taylor_two {f : ℝ → ℝ} {a b K : ℝ}
    (hf : ∀ z ∈ Icc a b, ContDiffAt ℝ 2 f z)
    {ι : Type*} {l : Filter ι} {x : ι → ℕ → ℝ} {n : ι → ℕ} {δ : ι → ℝ}
    (hx : ∀ᶠ k in l, ∀ i ≤ n k, x k i ∈ Icc a b)
    (hδ : ∀ᶠ k in l, ∀ i < n k, |x k (i + 1) - x k i| ≤ δ k)
    (hδ0 : Tendsto δ l (𝓝 0))
    (hQ : ∀ᶠ k in l, ∑ i ∈ Finset.range (n k), (x k (i + 1) - x k i) ^ 2 ≤ K) :
    Tendsto (fun k ↦ f (x k (n k)) - f (x k 0) -
      (∑ i ∈ Finset.range (n k), deriv f (x k i) * (x k (i + 1) - x k i)) -
      1 / 2 * ∑ i ∈ Finset.range (n k),
        deriv (deriv f) (x k i) * (x k (i + 1) - x k i) ^ 2) l (𝓝 0) := by
  simp_rw [sub_sum_taylor_two_eq_sum_sub_taylorWithinEval]
  have hK : 0 ≤ max K 0 := le_max_right _ _
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨η, hη, hTaylor⟩ := exists_pos_forall_abs_sub_taylorWithinEval_two_le
    hf (div_pos hε (by positivity : 0 < max K 0 + 1))
  filter_upwards [(tendsto_order.1 hδ0).2 η hη, hx, hδ, hQ] with k hk hxk hδk hQk
  have hstep i (hi : i ∈ Finset.range (n k)) :
      ‖f (x k (i + 1)) - taylorWithinEval f 2 univ (x k i) (x k (i + 1))‖ ≤
        ε / (max K 0 + 1) * (x k (i + 1) - x k i) ^ 2 := by
    have hi' := Finset.mem_range.1 hi
    simpa only [Real.norm_eq_abs] using
      hTaylor _ (hxk i hi'.le) _ (hxk (i + 1) hi') ((hδk i hi').trans_lt hk)
  have hbound : |∑ i ∈ Finset.range (n k),
      (f (x k (i + 1)) - taylorWithinEval f 2 univ (x k i) (x k (i + 1)))| ≤
      ε / (max K 0 + 1) * max K 0 := by
    calc
      _ ≤ ε / (max K 0 + 1) *
          ∑ i ∈ Finset.range (n k), (x k (i + 1) - x k i) ^ 2 := by
        simpa only [Real.norm_eq_abs, ← Finset.mul_sum] using
          norm_sum_le_of_le (Finset.range (n k)) hstep
      _ ≤ _ := by gcongr; exact hQk.trans (le_max_left _ _)
  rw [Real.dist_eq, sub_zero]
  exact hbound.trans_lt (by
    have hK1 : 0 < max K 0 + 1 := by positivity
    have := div_mul_cancel₀ ε hK1.ne'
    nlinarith [div_pos hε hK1])

end TauCeti
