/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.VectorMeasure.RiemannSums
public import TauCeti.MeasureTheory.VectorMeasure.FiniteHorizon

/-!
# Uniform approximation of accumulated Stieltjes integrals

Clip each cell of a finite grid at an observation time `t`, keeping its original tag.
For a continuous integrand and a finite-variation vector measure, these sums converge
uniformly over the entire horizon to the accumulated integral on `(a,t]`. The estimate
uses only the integrand's oscillation on the original cells and the variation on the
full horizon; the number of cells does not enter it.

For right-continuous BV paths this gives uniform convergence of truncated
Riemann–Stieltjes sums, including their last partial cell. Jumps of the integrator are
allowed, the initial atom is excluded, and terminal jumps are included. This pathwise
limit identifies finite-variation terms in process-level integration formulas. It does
not assert uniform convergence of sums whose last cell overshoots the observation time.

## References

* Philip Protter, *Stochastic Integration and Differential Equations*, second edition,
  Chapter I, finite-variation integration.
-/

public section

open MeasureTheory Set Filter Topology
open scoped BigOperators

/-- Truncated tagged Riemann–Stieltjes sums converge uniformly on the closed horizon
for a continuous integrand and a right-continuous BV integrator. No behavior outside
the horizon is assumed. Repeated dates, empty grids and integrator jumps are allowed. -/
theorem BoundedVariationOn.tendstoUniformlyOn_sum_tagged_min_sub
    {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {g : ℝ → F} {a b : ℝ} (hg : BoundedVariationOn g (Icc a b)) (hab : a ≤ b)
    {f : ℝ → E} (hf : ContinuousOn f (Icc a b))
    (hgr : ∀ x ∈ Icc a b, ContinuousWithinAt g (Icc x b) x)
    (B : E →L[ℝ] F →L[ℝ] G) {l : Filter ι} {n : ι → ℕ} {τ ξ : ι → ℕ → ℝ}
    (hτ : ∀ k, Monotone (τ k)) (h₀ : ∀ k, τ k 0 = a) (hn : ∀ k, τ k (n k) = b)
    (hξ : ∀ k i, i < n k → ξ k i ∈ Icc (τ k i) (τ k (i + 1)))
    {δ : ι → ℝ} (hmesh : ∀ k i, i < n k → τ k (i + 1) - τ k i ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    TendstoUniformlyOn (fun k t ↦ ∑ i ∈ Finset.range (n k),
      B (f (ξ k i)) (g (min (τ k (i + 1)) t) - g (min (τ k i) t)))
      (fun t ↦ ∫ᵛ x in Ioc a t, f x ∂[B; hg.vectorMeasureIcc hab]) l (Icc a b) := by
  apply (MeasureTheory.VectorMeasure.tendstoUniformlyOn_sum_tagged_min_Ioc
    (μ := hg.vectorMeasureIcc hab) (B := B) hf hτ h₀ hn hξ hmesh hδ).congr
  filter_upwards [] with k t ht
  have hcell := (hτ k).mapsTo_Icc (a := 0) (b := n k)
  rw [h₀ k, hn k] at hcell
  apply Finset.sum_congr rfl
  intro i hi
  have hleft := hcell ⟨Nat.zero_le _, (Finset.mem_range.1 hi).le⟩
  have hright := hcell ⟨Nat.zero_le _, Finset.mem_range.1 hi⟩
  have hleft' : min (τ k i) t ∈ Icc a b :=
    ⟨le_min hleft.1 ht.1, (min_le_left _ _).trans hleft.2⟩
  have hright' : min (τ k (i + 1)) t ∈ Icc a b :=
    ⟨le_min hright.1 ht.1, (min_le_left _ _).trans hright.2⟩
  rw [hg.vectorMeasureIcc_Ioc hab (hgr _ hleft') (hgr _ hright') hleft' hright'
    (min_le_min_right t (hτ k (Nat.le_succ i)))]
