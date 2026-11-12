/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Taylor.Basic

/-!
# Parameter-uniform spatial Taylor remainders

For a family of scalar functions, continuity of the spatial second derivative on a compact
parameter/state cylinder gives a uniform quadratic remainder estimate. Summing these estimates
along grids with vanishing increments and bounded quadratic sums gives a vanishing remainder,
even when the parameter changes at every step.

In time-dependent change-of-variables formulas the parameter is time. Only spatial C²
regularity and joint continuity of the spatial second derivative enter this estimate; no
second time derivative or mixed derivative is required. The time-coordinate increments are
separate from the spatial remainders treated here.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

/-- Spatial Taylor remainders with changing parameters tend to zero along finite grids whose
increments vanish and whose quadratic sums are eventually bounded. Parameters may vary
arbitrarily in a fixed compact set, without converging or being ordered. -/
theorem tendsto_sum_sub_taylorWithinEval_two_param
    {A : Type*} [PseudoMetricSpace A] {s : Set A} (hs : IsCompact s)
    {f : A → ℝ → ℝ} {a b K : ℝ}
    (hf : ∀ u ∈ s, ∀ z ∈ Icc a b, ContDiffAt ℝ 2 (f u) z)
    (h₂ : ContinuousOn (fun p : A × ℝ ↦ iteratedDeriv 2 (f p.1) p.2) (s ×ˢ Icc a b))
    {ι : Type*} {l : Filter ι} {n : ι → ℕ}
    {u : ∀ k, Fin (n k) → A} {x y : ∀ k, Fin (n k) → ℝ} {δ : ι → ℝ}
    (hu : ∀ᶠ k in l, ∀ i, u k i ∈ s)
    (hx : ∀ᶠ k in l, ∀ i, x k i ∈ Icc a b)
    (hy : ∀ᶠ k in l, ∀ i, y k i ∈ Icc a b)
    (hδ : ∀ᶠ k in l, ∀ i, |y k i - x k i| ≤ δ k)
    (hδ0 : Tendsto δ l (𝓝 0))
    (hQ : ∀ᶠ k in l, ∑ i, (y k i - x k i) ^ 2 ≤ K) :
    Tendsto (fun k ↦ ∑ i, (f (u k i) (y k i) -
      taylorWithinEval (f (u k i)) 2 univ (x k i) (y k i))) l (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨η, hη, hTaylor⟩ := exists_pos_forall_abs_sub_taylorWithinEval_two_le_param
    hs hf h₂ (div_pos hε (by positivity : 0 < max K 0 + 1))
  filter_upwards [(tendsto_order.1 hδ0).2 η hη, hu, hx, hy, hδ, hQ]
    with k hk huk hxk hyk hδk hQk
  have hbound : |∑ i, (f (u k i) (y k i) -
      taylorWithinEval (f (u k i)) 2 univ (x k i) (y k i))| ≤
      ε / (max K 0 + 1) * max K 0 := by
    calc
      _ ≤ ε / (max K 0 + 1) * ∑ i, (y k i - x k i) ^ 2 := by
        have hstep (i : Fin (n k)) (_ : i ∈ Finset.univ) :
            ‖f (u k i) (y k i) - taylorWithinEval (f (u k i)) 2 univ (x k i) (y k i)‖ ≤
              ε / (max K 0 + 1) * (y k i - x k i) ^ 2 := by
          simpa only [Real.norm_eq_abs] using
            hTaylor _ (huk i) _ (hxk i) _ (hyk i) ((hδk i).trans_lt hk)
        simpa only [Real.norm_eq_abs, ← Finset.mul_sum] using
          norm_sum_le_of_le Finset.univ hstep
      _ ≤ _ := by gcongr; exact hQk.trans (le_max_left _ _)
  rw [Real.dist_eq, sub_zero]
  apply hbound.trans_lt
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < max K 0 + 1)]
  linarith

end TauCeti
