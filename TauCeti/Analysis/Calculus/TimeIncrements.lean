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
at its endpoints. The estimates hold for Banach-valued functions. The finite-grid error
bound needs only cellwise derivatives and integrability, with no topology on the states;
convergence along a continuous path requires only a topological state space.

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
  {f g : ℝ → E → F} {X : ℝ → E} {a b : ℝ}

/-- A uniform bound on the error in the frozen-state time derivative bounds the error
of the summed time increments by that bound times the elapsed time. -/
theorem norm_sum_time_increment_sub_integral_le
    {τ : ℕ → ℝ} {n : ℕ} (hτ : MonotoneOn τ (Iic n)) {z : ℕ → E}
    (hf : ∀ i < n, ∀ t ∈ Icc (τ i) (τ (i + 1)),
      HasDerivWithinAt (fun u ↦ f u (z i)) (g t (z i)) (Icc (τ i) (τ (i + 1))) t)
    (hgz : ∀ i < n, IntervalIntegrable (fun t ↦ g t (z i)) volume (τ i) (τ (i + 1)))
    (hgX : IntervalIntegrable (fun t ↦ g t (X t)) volume (τ 0) (τ n)) {ε : ℝ}
    (hε : ∀ i < n, ∀ t ∈ Ioc (τ i) (τ (i + 1)), ‖g t (z i) - g t (X t)‖ ≤ ε) :
    ‖(∑ i ∈ Finset.range n, (f (τ (i + 1)) (z i) - f (τ i) (z i))) -
      ∫ t in τ 0..τ n, g t (X t)‖ ≤ ε * (τ n - τ 0) := by
  have hint (i : ℕ) (hi : i < n) :
      IntervalIntegrable (fun t ↦ g t (X t)) volume (τ i) (τ (i + 1)) := by
    apply hgX.mono_set
    rw [uIcc_of_le (hτ hi.le hi (by omega)),
      uIcc_of_le (hτ (by simp) (by simp) (Nat.zero_le n))]
    exact Icc_subset_Icc (hτ (by simp) hi.le (Nat.zero_le i)) (hτ hi (by simp) hi)
  rw [← intervalIntegral.sum_integral_adjacent_intervals hint, ← Finset.sum_sub_distrib]
  have hstep (i : ℕ) (hi : i ∈ Finset.range n) :
      ‖f (τ (i + 1)) (z i) - f (τ i) (z i) -
        ∫ t in τ i..τ (i + 1), g t (X t)‖ ≤ ε * (τ (i + 1) - τ i) := by
    have hi' := Finset.mem_range.mp hi
    have hle : τ i ≤ τ (i + 1) := hτ hi'.le hi' (by omega)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle
      (fun t ht ↦ (hf i hi' t ht).continuousWithinAt)
      (fun t ht ↦ (hf i hi' t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)) (hgz i hi')
    rw [← hFTC, ← intervalIntegral.integral_sub (hgz i hi') (hint i hi')]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht ↦ hε i hi' t ((uIoc_of_le hle) ▸ ht))
    rwa [abs_of_nonneg (sub_nonneg.mpr hle)] at hb
  calc
    _ ≤ ∑ i ∈ Finset.range n, ε * (τ (i + 1) - τ i) := norm_sum_le_of_le _ hstep
    _ = ε * (τ n - τ 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]

/-- Freezing a continuous state path at arbitrary tags in vanishing time cells gives the
correct integral of the time derivative. The index filter and grids need not be countable
or nested, grid conditions need hold only eventually, and no spatial differentiability
is assumed. -/
theorem tendsto_sum_time_increment [TopologicalSpace E]
    (hX : ContinuousOn X (Icc a b))
    (hg : ContinuousOn (Function.uncurry g) (Icc a b ×ˢ (X '' Icc a b)))
    (hf : ∀ x ∈ X '' Icc a b, ∀ t ∈ Icc a b,
      HasDerivWithinAt (fun u ↦ f u x) (g t x) (Icc a b) t)
    {ι : Type*} {l : Filter ι} {τ : ι → ℕ → ℝ} {n : ι → ℕ}
    {θ : ι → ℕ → ℝ} {mesh : ι → ℝ}
    (hτ : ∀ᶠ k in l, MonotoneOn (τ k) (Iic (n k)))
    (hτ₀ : ∀ᶠ k in l, τ k 0 = a) (hτn : ∀ᶠ k in l, τ k (n k) = b)
    (hθ : ∀ᶠ k in l, ∀ i < n k, θ k i ∈ Icc (τ k i) (τ k (i + 1)))
    (hmesh : ∀ᶠ k in l, ∀ i < n k, τ k (i + 1) - τ k i ≤ mesh k)
    (hlim : Tendsto mesh l (𝓝 0)) :
    Tendsto (fun k ↦ ∑ i ∈ Finset.range (n k),
      (f (τ k (i + 1)) (X (θ k i)) - f (τ k i) (X (θ k i)))) l
      (𝓝 (∫ t in a..b, g t (X t))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let c := ε / (|b - a| + 1)
  have hc : 0 < c := div_pos hε (by positivity)
  have hcomp : ContinuousOn (fun p : ℝ × ℝ ↦ g p.1 (X p.2)) (Icc a b ×ˢ Icc a b) :=
    hg.comp (continuousOn_fst.prodMk
      (hX.comp continuousOn_snd (fun _ (hp : _ ∈ Icc a b ×ˢ Icc a b) ↦ hp.2)))
      (fun _ hp ↦ ⟨hp.1, mem_image_of_mem X hp.2⟩)
  obtain ⟨η, hη, hgη⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcomp) c hc
  filter_upwards [(tendsto_order.mp hlim).2 η hη, hτ, hτ₀, hτn, hθ, hmesh]
    with k hk hτ hτ₀ hτn hθ hmesh
  have hcell (i : ℕ) (hi : i < n k) : Icc (τ k i) (τ k (i + 1)) ⊆ Icc a b := by
    exact Icc_subset_Icc (hτ₀ ▸ hτ (by simp) hi.le (Nat.zero_le i))
      (hτn ▸ hτ hi (by simp) hi)
  have hpath : ContinuousOn (fun t ↦ g t (X t)) (Icc a b) :=
    hg.comp (continuousOn_id.prodMk hX) (fun _ ht ↦ ⟨ht, mem_image_of_mem X ht⟩)
  have hab : a ≤ b := hτ₀ ▸ hτn ▸ hτ (by simp) (by simp) (Nat.zero_le (n k))
  have hbound := norm_sum_time_increment_sub_integral_le hτ
    (fun i hi t ht ↦ (hf _ (mem_image_of_mem X (hcell i hi (hθ i hi))) _
      (hcell i hi ht)).mono (hcell i hi))
    (fun i hi ↦ (hg.comp (continuousOn_id.prodMk continuousOn_const)
      (fun _ ht ↦
        ⟨hcell i hi ht, mem_image_of_mem X (hcell i hi (hθ i hi))⟩)).intervalIntegrable_of_Icc
          (hτ hi.le hi (by omega)))
    (by simpa only [hτ₀, hτn] using hpath.intervalIntegrable_of_Icc hab)
    (ε := c) (fun i hi t ht ↦ ?_)
  · rw [hτ₀, hτn] at hbound
    rw [dist_eq_norm]
    apply hbound.trans_lt
    calc
      c * (b - a) ≤ c * |b - a| := mul_le_mul_of_nonneg_left (le_abs_self _) hc.le
      _ < ε := by
        dsimp [c]
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : 0 < |b - a| + 1)]
        linarith
  · have ht' : t ∈ Icc (τ k i) (τ k (i + 1)) := Ioc_subset_Icc_self ht
    have hdist : dist (θ k i) t < η := by
      rw [Real.dist_eq]
      exact (abs_le.mpr ⟨by linarith [(hθ i hi).1, ht'.2],
        by linarith [(hθ i hi).2, ht'.1]⟩).trans_lt ((hmesh i hi).trans_lt hk)
    have hp := hgη (t, θ k i) ⟨hcell i hi ht', hcell i hi (hθ i hi)⟩
      (t, t) ⟨hcell i hi ht', hcell i hi ht'⟩ (by simpa using hdist)
    simpa only [dist_eq_norm] using hp.le

end TauCeti
