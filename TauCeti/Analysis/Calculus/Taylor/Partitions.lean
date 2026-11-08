/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Taylor.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Accumulated Taylor remainders

Second-order Taylor errors can be summed along finite grids without a bound on the number of
grid points. For a C³ function with bounded third derivative, the error is bounded by the
largest increment times the sum of squared increments. For a C² function, uniform continuity
of the second derivative on a compact interval gives a vanishing coefficient instead.
Consequently, if the largest increment tends to zero and the quadratic sums remain bounded,
the accumulated remainder tends to zero. The grids may contain repetitions or be empty.

These are deterministic estimates for the Taylor-expansion step in change-of-variables
formulas along paths with controlled quadratic sums. They do not assert convergence of the
first- or second-order sums separately.

The one-step expansion uses Mathlib's Taylor theorem with Lagrange remainder.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

/-- Uniform second-order Taylor remainder estimate on a compact interval for a C² function.
The coefficient of the squared increment can be made arbitrarily small. -/
theorem exists_pos_forall_abs_sub_taylorWithinEval_two_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |y - x| < δ →
      |f y - taylorWithinEval f 2 univ x y| ≤ ε * (y - x) ^ 2 := by
  have hu : UniformContinuousOn (iteratedDeriv 2 f) (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hf.continuous_iteratedDeriv' 2).continuousOn
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1 hu ε hε
  refine ⟨δ, hδ, fun x hx y hy hxy ↦ ?_⟩
  by_cases h : x = y
  · subst y
    simp
  obtain ⟨z, hz, hTaylor⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) h hf.contDiffOn
  have hz' : z ∈ Icc a b := uIcc_subset_Icc hx hy (uIoo_subset_uIcc_self hz)
  have hzx : dist z x < δ := lt_of_le_of_lt
    (by simpa [Real.dist_eq] using abs_sub_left_of_mem_uIcc (uIoo_subset_uIcc_self hz)) hxy
  have hd : |iteratedDeriv 2 f z - iteratedDeriv 2 f x| < ε := by
    simpa [Real.dist_eq] using hδf z hz' x hx hzx
  have hpoly : taylorWithinEval f 1 (uIcc x y) x y =
      f x + deriv f x * (y - x) := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc h)
        (hf.of_le (by norm_num)).contDiffAt left_mem_uIcc]
    simp [iteratedDeriv_one, smul_eq_mul, mul_comm]
  rw [hpoly] at hTaylor
  have heq : f y - taylorWithinEval f 2 univ x y =
      (iteratedDeriv 2 f z - iteratedDeriv 2 f x) * (y - x) ^ 2 / 2 := by
    simp [taylorWithinEval_succ, taylor_within_zero_eval, smul_eq_mul]
    norm_num at hTaylor
    linarith
  rw [heq, abs_div, abs_mul, abs_pow, sq_abs]
  norm_num
  nlinarith [mul_le_mul_of_nonneg_right hd.le (sq_nonneg (y - x))]

/-- A bounded third derivative controls the accumulated second-order Taylor remainder by
the largest increment and the quadratic sum, independently of the size of the finite grid. -/
theorem abs_sum_sub_taylorWithinEval_two_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    {M δ : ℝ} (hM : ∀ x, |iteratedDeriv 3 f x| ≤ M) (x : ℕ → ℝ) (n : ℕ)
    (hδ : ∀ i < n, |x (i + 1) - x i| ≤ δ) :
    |∑ i ∈ Finset.range n, (f (x (i + 1)) - taylorWithinEval f 2 univ (x i) (x (i + 1)))| ≤
      M / 6 * δ * ∑ i ∈ Finset.range n, (x (i + 1) - x i) ^ 2 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |f (x (i + 1)) - taylorWithinEval f 2 univ (x i) (x (i + 1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, M / 6 * δ * (x (i + 1) - x i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h := abs_sub_taylorWithinEval_le (n := 2) hf hM (x i) (x (i + 1))
      have hinc := hδ i (Finset.mem_range.1 hi)
      norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
      apply h.trans
      calc
        _ = |x (i + 1) - x i| * (M / 6 * (x (i + 1) - x i) ^ 2) := by
          rw [pow_succ, sq_abs]
          ring
        _ ≤ δ * (M / 6 * (x (i + 1) - x i) ^ 2) :=
          mul_le_mul_of_nonneg_right hinc (by positivity)
        _ = _ := by ring
    _ = _ := by rw [Finset.mul_sum]

/-- The sum of the first- and second-order Taylor terms approximates the endpoint increment
for C² functions on grids confined to a fixed compact interval, with vanishing increments
and uniformly bounded quadratic sums. No nesting, ordering, or bound on the number of grid
points is required. -/
theorem tendsto_sub_sum_taylor_two {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {a b K : ℝ} {x : ℕ → ℕ → ℝ} {n : ℕ → ℕ} {δ : ℕ → ℝ}
    (hx : ∀ k i, i ≤ n k → x k i ∈ Icc a b)
    (hδ : ∀ k i, i < n k → |x k (i + 1) - x k i| ≤ δ k)
    (hδ0 : Tendsto δ atTop (𝓝 0))
    (hQ : ∀ k, ∑ i ∈ Finset.range (n k), (x k (i + 1) - x k i) ^ 2 ≤ K) :
    Tendsto (fun k ↦ f (x k (n k)) - f (x k 0) -
      (∑ i ∈ Finset.range (n k), deriv f (x k i) * (x k (i + 1) - x k i)) -
      1 / 2 * ∑ i ∈ Finset.range (n k),
        deriv (deriv f) (x k i) * (x k (i + 1) - x k i) ^ 2) atTop (𝓝 0) := by
  have htel k : f (x k (n k)) - f (x k 0) -
      (∑ i ∈ Finset.range (n k), deriv f (x k i) * (x k (i + 1) - x k i)) -
      1 / 2 * (∑ i ∈ Finset.range (n k),
        deriv (deriv f) (x k i) * (x k (i + 1) - x k i) ^ 2) =
      ∑ i ∈ Finset.range (n k),
        (f (x k (i + 1)) - taylorWithinEval f 2 univ (x k i) (x k (i + 1))) := by
    rw [← Finset.sum_range_sub (fun i ↦ f (x k i)) (n k), ← Finset.sum_sub_distrib,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp [taylorWithinEval_succ, taylor_within_zero_eval, iteratedDeriv_succ, smul_eq_mul]
    ring
  simp_rw [htel]
  have hK : 0 ≤ K := (Finset.sum_nonneg fun i _ ↦ sq_nonneg _).trans (hQ 0)
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨η, hη, hTaylor⟩ := exists_pos_forall_abs_sub_taylorWithinEval_two_le
    hf a b (div_pos hε (by positivity : 0 < K + 1))
  filter_upwards [(tendsto_order.1 hδ0).2 η hη] with k hk
  have hbound : |∑ i ∈ Finset.range (n k),
      (f (x k (i + 1)) - taylorWithinEval f 2 univ (x k i) (x k (i + 1)))| ≤
      ε / (K + 1) * K := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n k),
          |f (x k (i + 1)) - taylorWithinEval f 2 univ (x k i) (x k (i + 1))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (n k), ε / (K + 1) * (x k (i + 1) - x k i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' := Finset.mem_range.1 hi
        exact hTaylor _ (hx k i hi'.le) _ (hx k (i + 1) hi')
          ((hδ k i hi').trans_lt hk)
      _ ≤ _ := by rw [← Finset.mul_sum]; gcongr; exact hQ k
  rw [Real.dist_eq, sub_zero]
  exact hbound.trans_lt (by
    have hK1 : 0 < K + 1 := by positivity
    have := div_mul_cancel₀ ε hK1.ne'
    nlinarith [div_pos hε hK1])

end TauCeti
