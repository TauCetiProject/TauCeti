/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.VectorMeasure.RiemannSums
public import TauCeti.MeasureTheory.VectorMeasure.FiniteHorizon
public import Mathlib.Topology.MetricSpace.UniformConvergence

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

namespace MeasureTheory.VectorMeasure

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {μ : VectorMeasure ℝ F} [IsFiniteMeasure μ.variation]
  {B : E →L[ℝ] F →L[ℝ] G} {f : ℝ → E}

/-- The error of a clipped tagged sum is controlled uniformly in the observation time
by the oscillation on the original cells and the variation on the full horizon. -/
theorem norm_sum_min_sub_setIntegral_Ioc_le {n : ℕ} {τ ξ : ℕ → ℝ}
    (hτ : Monotone τ) (hf : μ.IntegrableOn f (Ioc (τ 0) (τ n))) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ i < n, ∀ x ∈ Ioc (τ i) (τ (i + 1)), ‖f (ξ i) - f x‖ ≤ ε)
    {t : ℝ} (ht : t ∈ Icc (τ 0) (τ n)) :
    ‖(∑ i ∈ Finset.range n,
        B (f (ξ i)) (μ (Ioc (min (τ i) t) (min (τ (i + 1)) t)))) -
      ∫ᵛ x in Ioc (τ 0) t, f x ∂[B; μ]‖ ≤
        ε * ‖B‖ * μ.variation.real (Ioc (τ 0) (τ n)) := by
  have hclip : Monotone (fun i ↦ min (τ i) t) := hτ.min monotone_const
  have hfi : μ.IntegrableOn f (Ioc (min (τ 0) t) (min (τ n) t)) := by
    rw [min_eq_left ht.1, min_eq_right ht.2]
    exact hf.mono measurableSet_Ioc (Ioc_subset_Ioc_right ht.2)
  have herr := norm_sum_sub_setIntegral_Ioc_le (B := B) hclip hfi
    (ξ := ξ) (ε := ε) (fun i hi x hx ↦ hosc i hi x (by grind))
  rw [min_eq_left ht.1, min_eq_right ht.2] at herr
  exact herr.trans (mul_le_mul_of_nonneg_left
    (measureReal_mono (Ioc_subset_Ioc_right ht.2)) (mul_nonneg hε (norm_nonneg B)))

/-- Tagged vector-measure sums clipped at `t` converge uniformly for all `t` in the
horizon. Original tags may be either endpoint or any point of their original cell,
even if the tag lies after `t` in the last partial cell. -/
theorem tendstoUniformlyOn_sum_tagged_min_Ioc {ι : Type*} {l : Filter ι} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) {n : ι → ℕ} {τ ξ : ι → ℕ → ℝ}
    (hτ : ∀ k, Monotone (τ k)) (h₀ : ∀ k, τ k 0 = a) (hn : ∀ k, τ k (n k) = b)
    (hξ : ∀ k i, i < n k → ξ k i ∈ Icc (τ k i) (τ k (i + 1)))
    {δ : ι → ℝ} (hmesh : ∀ k i, i < n k → τ k (i + 1) - τ k i ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    TendstoUniformlyOn (fun k t ↦ ∑ i ∈ Finset.range (n k),
      B (f (ξ k i)) (μ (Ioc (min (τ k i) t) (min (τ k (i + 1)) t))))
      (fun t ↦ ∫ᵛ x in Ioc a t, f x ∂[B; μ]) l (Icc a b) := by
  let C := ‖B‖ * μ.variation.real (Ioc a b)
  have hfi : μ.IntegrableOn f (Ioc a b) := by
    apply (integrable_indicator_iff measurableSet_Ioc).1
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Ioc).2
      ((hf.integrableOn_Icc (μ := μ.variation)).mono_set Ioc_subset_Icc_self)
  apply Metric.tendstoUniformlyOn_iff.2
  intro ε hε
  -- One modulus of continuity controls all cells at all observation times.
  obtain ⟨d, hd, hosc⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) (ε / (C + 1)) (by positivity)
  filter_upwards [hδ.eventually (gt_mem_nhds hd)] with k hk t ht
  have hcell (i : ℕ) (hi : i ≤ n k) : τ k i ∈ Icc a b := by
    simpa only [h₀ k, hn k] using (hτ k).mapsTo_Icc ⟨Nat.zero_le i, hi⟩
  have hosc' (i : ℕ) (hi : i < n k) (x : ℝ)
      (hx : x ∈ Ioc (τ k i) (τ k (i + 1))) : ‖f (ξ k i) - f x‖ ≤ ε / (C + 1) := by
    have htag := hξ k i hi
    have hx' : x ∈ Icc a b := ⟨(hcell i hi.le).1.trans hx.1.le,
      hx.2.trans (hcell (i + 1) hi).2⟩
    have htag' : ξ k i ∈ Icc a b := ⟨(hcell i hi.le).1.trans htag.1,
      htag.2.trans (hcell (i + 1) hi).2⟩
    rw [← dist_eq_norm]
    apply (hosc _ htag' _ hx' ?_).le
    rw [Real.dist_eq, abs_lt]
    have hlen := (hmesh k i hi).trans_lt hk
    constructor <;> linarith [htag.1, htag.2, hx.1, hx.2]
  have herr := norm_sum_min_sub_setIntegral_Ioc_le (B := B) (hτ k)
    (by simpa only [h₀ k, hn k] using hfi) (by positivity : 0 ≤ ε / (C + 1)) hosc'
    (by simpa only [h₀ k, hn k] using ht)
  simp only [h₀ k, hn k] at herr
  rw [dist_comm, dist_eq_norm]
  apply herr.trans_lt
  calc
    ε / (C + 1) * ‖B‖ * μ.variation.real (Ioc a b) = ε / (C + 1) * C := by
      dsimp [C]
      ring
    _ < ε := by
      have hC₁ : 0 < C + 1 := by positivity
      rw [div_mul_eq_mul_div, div_lt_iff₀ hC₁]
      nlinarith [hε]

end MeasureTheory.VectorMeasure

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
  have hcell (k : ι) (i : ℕ) (hi : i ≤ n k) : τ k i ∈ Icc a b := by
    simpa only [h₀ k, hn k] using (hτ k).mapsTo_Icc ⟨Nat.zero_le i, hi⟩
  apply (MeasureTheory.VectorMeasure.tendstoUniformlyOn_sum_tagged_min_Ioc
    (μ := hg.vectorMeasureIcc hab) (B := B) hf hτ h₀ hn hξ hmesh hδ).congr
  filter_upwards [] with k t ht
  apply Finset.sum_congr rfl
  intro i hi
  have hleft := hcell k i (Finset.mem_range.1 hi).le
  have hright := hcell k (i + 1) (Finset.mem_range.1 hi)
  have hleft' : min (τ k i) t ∈ Icc a b :=
    ⟨le_min hleft.1 ht.1, (min_le_left _ _).trans hleft.2⟩
  have hright' : min (τ k (i + 1)) t ∈ Icc a b :=
    ⟨le_min hright.1 ht.1, (min_le_left _ _).trans hright.2⟩
  rw [hg.vectorMeasureIcc_Ioc hab (hgr _ hleft') (hgr _ hright') hleft' hright'
    (min_le_min_right t (hτ k (Nat.le_succ i)))]
