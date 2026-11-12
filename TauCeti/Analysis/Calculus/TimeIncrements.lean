/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Time increments along continuous paths

For a function with a continuous time derivative, sum the time increments while freezing
the state at a tag in each time cell. Along a continuous state path these sums converge to
the ordinary integral of the time derivative evaluated on the path. No spatial derivative
or variation bound on the path is required.

This is the deterministic time-coordinate limit in time-dependent change-of-variables
formulas. Tags may be either endpoint or any point of the cell, and grids may have repeated
dates. Time derivatives are taken within the closed horizon, allowing one-sided derivatives
at its endpoints. The estimates hold for Banach-valued functions, with topological states
for the error bound and pseudometric states for convergence.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second
  edition, Springer, 1991, §3.3.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace TauCeti

variable {E F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f g : ℝ → E → F} {X : ℝ → E} {K : Set E} {a b : ℝ}

/-- A uniform bound on the error in the frozen-state time derivative bounds the error
of the summed time increments by that bound times the elapsed time. -/
theorem norm_sum_time_increment_sub_integral_le [TopologicalSpace E]
    (hg : ContinuousOn (Function.uncurry g) (Icc a b ×ˢ K))
    (hf : ∀ x ∈ K, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun u ↦ f u x) (g t x) (Icc a b) t)
    (hX : ContinuousOn X (Icc a b)) (hXK : MapsTo X (Icc a b) K)
    {τ : ℕ → ℝ} {n : ℕ} (hτ : MonotoneOn τ (Iic n))
    (hτ₀ : τ 0 = a) (hτn : τ n = b) {z : ℕ → E}
    (hz : ∀ i < n, z i ∈ K) {ε : ℝ}
    (hε : ∀ i < n, ∀ t ∈ Icc (τ i) (τ (i + 1)), ‖g t (z i) - g t (X t)‖ ≤ ε) :
    ‖(∑ i ∈ Finset.range n, (f (τ (i + 1)) (z i) - f (τ i) (z i))) -
      ∫ t in a..b, g t (X t)‖ ≤ ε * (b - a) := by
  have hcell (i : ℕ) (hi : i < n) : Icc (τ i) (τ (i + 1)) ⊆ Icc a b := by
    exact Icc_subset_Icc (hτ₀ ▸ hτ (by simp) hi.le (Nat.zero_le i))
      (hτn ▸ hτ hi (by simp) hi)
  have hpath : ContinuousOn (fun t ↦ g t (X t)) (Icc a b) :=
    hg.comp (continuousOn_id.prodMk hX) (fun t ht ↦ ⟨ht, hXK ht⟩)
  have hint (i : ℕ) (hi : i < n) :
      IntervalIntegrable (fun t ↦ g t (X t)) volume (τ i) (τ (i + 1)) :=
    (hpath.mono (hcell i hi)).intervalIntegrable_of_Icc (hτ hi.le hi (by omega))
  rw [← hτ₀, ← hτn, ← intervalIntegral.sum_integral_adjacent_intervals hint,
    ← Finset.sum_sub_distrib]
  have hstep (i : ℕ) (hi : i ∈ Finset.range n) :
      ‖f (τ (i + 1)) (z i) - f (τ i) (z i) -
        ∫ t in τ i..τ (i + 1), g t (X t)‖ ≤ ε * (τ (i + 1) - τ i) := by
    have hi' := Finset.mem_range.mp hi
    have hle : τ i ≤ τ (i + 1) := hτ hi'.le hi' (by omega)
    have hc : ContinuousOn (fun t ↦ g t (z i)) (Icc (τ i) (τ (i + 1))) :=
      hg.comp (continuousOn_id.prodMk continuousOn_const) (fun t ht ↦
        ⟨hcell i hi' ht, hz i hi'⟩)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle
      (fun t ht ↦ (hf _ (hz i hi') _ (hcell i hi' ht)).continuousWithinAt.mono (hcell i hi'))
      (fun t ht ↦ (hf _ (hz i hi') _ (hcell i hi' (Ioo_subset_Icc_self ht))).hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt (hcell i hi' ⟨le_rfl, hle⟩).1 ht.1)
          (lt_of_lt_of_le ht.2 (hcell i hi' ⟨hle, le_rfl⟩).2)))
      (hc.intervalIntegrable_of_Icc hle)
    rw [← hFTC, ← intervalIntegral.integral_sub (hc.intervalIntegrable_of_Icc hle) (hint i hi')]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht ↦ hε i hi' t
        ((uIcc_of_le hle) ▸ (uIoc_subset_uIcc (a := τ i) (b := τ (i + 1)) ht)))
    rwa [abs_of_nonneg (sub_nonneg.mpr hle)] at hb
  calc
    _ ≤ ∑ i ∈ Finset.range n, ε * (τ (i + 1) - τ i) := norm_sum_le_of_le _ hstep
    _ = ε * (τ n - τ 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]

/-- Freezing a continuous state path at arbitrary tags in vanishing time cells gives the
correct integral of the time derivative. The index filter and grids need not be countable
or nested, and no spatial differentiability is assumed. -/
theorem tendsto_sum_time_increment [PseudoMetricSpace E]
    (hX : ContinuousOn X (Icc a b))
    (hg : ContinuousOn (Function.uncurry g) (Icc a b ×ˢ (X '' Icc a b)))
    (hf : ∀ x ∈ X '' Icc a b, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun u ↦ f u x) (g t x) (Icc a b) t)
    {ι : Type*} {l : Filter ι} {τ : ι → ℕ → ℝ} {n : ι → ℕ}
    {θ : ι → ℕ → ℝ} {mesh : ι → ℝ}
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k)))
    (hτ₀ : ∀ k, τ k 0 = a) (hτn : ∀ k, τ k (n k) = b)
    (hθ : ∀ k i, i < n k → θ k i ∈ Icc (τ k i) (τ k (i + 1)))
    (hmesh : ∀ k i, i < n k → τ k (i + 1) - τ k i ≤ mesh k)
    (hlim : Tendsto mesh l (𝓝 0)) :
    Tendsto (fun k ↦ ∑ i ∈ Finset.range (n k),
      (f (τ k (i + 1)) (X (θ k i)) - f (τ k i) (X (θ k i)))) l
      (𝓝 (∫ t in a..b, g t (X t))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let c := ε / (|b - a| + 1)
  have hc : 0 < c := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc.prod (isCompact_Icc.image_of_continuousOn hX)).uniformContinuousOn_of_continuous
      hg) c hc
  obtain ⟨η, hη, hXη⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hX) δ hδ
  filter_upwards [(tendsto_order.mp hlim).2 η hη] with k hk
  have hcell (i : ℕ) (hi : i < n k) : Icc (τ k i) (τ k (i + 1)) ⊆ Icc a b := by
    exact Icc_subset_Icc (hτ₀ k ▸ hτ k (by simp) hi.le (Nat.zero_le i))
      (hτn k ▸ hτ k hi (by simp) hi)
  have hXK : MapsTo X (Icc a b) (X '' Icc a b) := fun _ ht ↦ mem_image_of_mem X ht
  have hbound := norm_sum_time_increment_sub_integral_le hg hf hX hXK (hτ k) (hτ₀ k)
    (hτn k) (fun i hi ↦ hXK (hcell i hi (hθ k i hi))) (ε := c) (fun i hi t ht ↦ ?_)
  · rw [dist_eq_norm]
    apply hbound.trans_lt
    calc
      c * (b - a) ≤ c * |b - a| := mul_le_mul_of_nonneg_left (le_abs_self _) hc.le
      _ < ε := by
        dsimp [c]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < |b - a| + 1)]
        linarith
  · have hdist : dist (θ k i) t < η := by
      rw [Real.dist_eq]
      exact (abs_le.mpr ⟨by linarith [(hθ k i hi).1, ht.2],
        by linarith [(hθ k i hi).2, ht.1]⟩).trans_lt ((hmesh k i hi).trans_lt hk)
    have hstate := hXη _ (hcell i hi (hθ k i hi)) _ (hcell i hi ht) hdist
    have hp := hgδ (t, X (θ k i)) ⟨hcell i hi ht, hXK (hcell i hi (hθ k i hi))⟩
      (t, X t) ⟨hcell i hi ht, hXK (hcell i hi ht)⟩ (by simpa using hstate)
    simpa only [dist_eq_norm, Function.uncurry_apply_pair] using hp.le

end TauCeti
