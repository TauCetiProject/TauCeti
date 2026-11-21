/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Extreme eigenvalues and weak spectral limits

Any open interval meeting the support of the weak limit of empirical spectral measures
eventually contains an eigenvalue. An asymptotic upper bound at a point of the support
gives convergence of the largest eigenvalue there, and an asymptotic lower bound gives
the corresponding convergence for the smallest eigenvalue.
-/

public section

open Filter MeasureTheory Set
open scoped Topology

namespace Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] {m : ι → Type*} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)] {l : Filter ι}
  {A : (i : ι) → Matrix (m i) (m i) 𝕜} {hA : ∀ i, (A i).IsHermitian}
  {μ : ProbabilityMeasure ℝ}

/-- Weak convergence of the empirical spectral measures forces an eigenvalue in each
open set intersecting the support of the limit, eventually. -/
theorem eventually_exists_eigenvalues₀_mem_of_tendsto_spectralMeasure
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ))
    {U : Set ℝ} (hU : IsOpen U) (hpos : 0 < (μ : Measure ℝ) U) :
    ∀ᶠ i in l, ∃ j, (hA i).eigenvalues₀ j ∈ U := by
  classical
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto h hU
  filter_upwards [eventually_lt_of_lt_liminf (hpos.trans_le hlim)] with i hi
  rw [spectralMeasure_eq_empiricalMeasureOfFintype_eigenvalues₀,
    TauCeti.Probability.empiricalMeasureOfFintype_apply hU.measurableSet] at hi
  by_contra! hz
  simp only [Set.indicator_of_notMem (hz _), Finset.sum_const_zero, mul_zero, lt_self_iff_false]
    at hi

/-- If the largest eigenvalue is eventually below every strict upper bound of a point
in the limiting spectral support, it converges to that point. -/
theorem tendsto_eigenvalues₀_bot_of_tendsto_spectralMeasure
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ))
    {c : ℝ} (hc : c ∈ (μ : Measure ℝ).support)
    (hupper : ∀ r > c, ∀ᶠ i in l, (hA i).eigenvalues₀ ⊥ < r) :
    Tendsto (fun i ↦ (hA i).eigenvalues₀ ⊥) l (𝓝 c) := by
  refine tendsto_order.2 ⟨fun r hr ↦ ?_, hupper⟩
  have hpos := (Measure.mem_support_iff_forall c).1 hc _ (Ioi_mem_nhds hr)
  filter_upwards [eventually_exists_eigenvalues₀_mem_of_tendsto_spectralMeasure h isOpen_Ioi hpos]
    with i hi
  obtain ⟨j, hj⟩ := hi
  exact hj.trans_le ((hA i).eigenvalues₀_antitone bot_le)

/-- If the smallest eigenvalue is eventually above every strict lower bound of a point
in the limiting spectral support, it converges to that point. -/
theorem tendsto_eigenvalues₀_top_of_tendsto_spectralMeasure
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ))
    {c : ℝ} (hc : c ∈ (μ : Measure ℝ).support)
    (hlower : ∀ r < c, ∀ᶠ i in l, r < (hA i).eigenvalues₀ ⊤) :
    Tendsto (fun i ↦ (hA i).eigenvalues₀ ⊤) l (𝓝 c) := by
  refine tendsto_order.2 ⟨hlower, fun r hr ↦ ?_⟩
  have hpos := (Measure.mem_support_iff_forall c).1 hc _ (Iio_mem_nhds hr)
  filter_upwards [eventually_exists_eigenvalues₀_mem_of_tendsto_spectralMeasure h isOpen_Iio hpos]
    with i hi
  obtain ⟨j, hj⟩ := hi
  exact ((hA i).eigenvalues₀_antitone le_top).trans_lt hj

end Matrix
