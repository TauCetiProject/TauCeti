/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Taylor.Parameter

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
  intro i _
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
    calc
      _ ≤ M * |x (i + 1) - x i| ^ 3 / 6 := by
        simpa [Nat.factorial] using
          abs_sub_taylorWithinEval_le (n := 2) (fun t ht ↦ hf t (hsub ht))
            (fun t ht ↦ hM t (hsub (uIoo_subset_uIcc_self ht)))
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
  simp_rw [← Fin.sum_univ_eq_sum_range]
  have h₂ : ContinuousOn (fun p : ℝ × ℝ ↦ iteratedDeriv 2 f p.2) ({0} ×ˢ Icc a b) := by
    intro p hp
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Function.comp_def] using
      ((((hf p.2 hp.2).derivWithin (m := 1) (by norm_num)).derivWithin
        (m := 0) (by norm_num)).continuousAt.comp continuousAt_snd).continuousWithinAt
  exact tendsto_sum_sub_taylorWithinEval_two_param
    (isCompact_singleton (x := (0 : ℝ))) (f := fun _ ↦ f) (K := K) (n := n)
    (fun _ _ ↦ hf) h₂
    (u := fun _ _ ↦ 0) (x := fun k i ↦ x k i) (y := fun k i ↦ x k (i + 1))
    (Eventually.of_forall fun _ _ ↦ mem_singleton 0)
    (hx.mono fun k hk i ↦ hk i i.isLt.le)
    (hx.mono fun k hk i ↦ hk (i + 1) i.isLt)
    (hδ.mono fun k hk i ↦ hk i i.isLt) hδ0
    (hQ.mono fun k hk ↦ by simpa only [← Fin.sum_univ_eq_sum_range] using hk)

end TauCeti
