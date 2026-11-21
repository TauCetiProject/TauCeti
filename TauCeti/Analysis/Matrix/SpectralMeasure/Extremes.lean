/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm

/-!
# Extreme eigenvalues and weak spectral limits

Any open interval meeting the support of the weak limit of empirical spectral measures
eventually contains an eigenvalue. An asymptotic upper bound at a point of the support
gives convergence of the largest eigenvalue there, and an asymptotic lower bound gives
the corresponding convergence for the smallest eigenvalue. If `c` and `-c` both lie in the
limiting support and the Euclidean operator norms are eventually below every `r > c`,
the largest and smallest eigenvalues converge to `c` and `-c`.
-/

public section

open Filter MeasureTheory Set
open scoped Topology Matrix.Norms.L2Operator

namespace Filter.Tendsto

open Matrix

variable {𝕜 ι : Type*} [RCLike 𝕜] {m : ι → Type*} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)] [∀ i, Nonempty (m i)] {l : Filter ι}
  {A : (i : ι) → Matrix (m i) (m i) 𝕜} {hA : ∀ i, (A i).IsHermitian}
  {μ : ProbabilityMeasure ℝ}

/-- Weak convergence of empirical spectral measures forces an eigenvalue in an open set
of positive limiting mass, eventually. -/
theorem eventually_exists_eigenvalues₀_mem
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ))
    {U : Set ℝ} (hU : IsOpen U) (hpos : 0 < (μ : Measure ℝ) U) :
    ∀ᶠ i in l, ∃ j, (hA i).eigenvalues₀ j ∈ U := by
  simp only [spectralMeasure_eq_empiricalMeasureOfFintype_eigenvalues₀] at h
  exact h.eventually_exists_mem_of_empiricalMeasureOfFintype hU hpos

/-- If the largest eigenvalue is eventually below every strict upper bound of a point
in the limiting spectral support, it converges to that point. -/
theorem eigenvalues₀_bot_of_eventually_lt
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ))
    {c : ℝ} (hc : c ∈ (μ : Measure ℝ).support)
    (hupper : ∀ r > c, ∀ᶠ i in l, (hA i).eigenvalues₀ ⊥ < r) :
    Tendsto (fun i ↦ (hA i).eigenvalues₀ ⊥) l (𝓝 c) := by
  refine tendsto_order.2 ⟨fun r hr ↦ ?_, hupper⟩
  have hpos := (Measure.mem_support_iff_forall c).1 hc _ (Ioi_mem_nhds hr)
  filter_upwards [h.eventually_exists_eigenvalues₀_mem isOpen_Ioi hpos]
    with i hi
  obtain ⟨j, hj⟩ := hi
  exact hj.trans_le ((hA i).eigenvalues₀_antitone bot_le)

/-- If the smallest eigenvalue is eventually above every strict lower bound of a point
in the limiting spectral support, it converges to that point. -/
theorem eigenvalues₀_top_of_eventually_gt
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ))
    {c : ℝ} (hc : c ∈ (μ : Measure ℝ).support)
    (hlower : ∀ r < c, ∀ᶠ i in l, r < (hA i).eigenvalues₀ ⊤) :
    Tendsto (fun i ↦ (hA i).eigenvalues₀ ⊤) l (𝓝 c) := by
  refine tendsto_order.2 ⟨hlower, fun r hr ↦ ?_⟩
  have hpos := (Measure.mem_support_iff_forall c).1 hc _ (Iio_mem_nhds hr)
  filter_upwards [h.eventually_exists_eigenvalues₀_mem isOpen_Iio hpos]
    with i hi
  obtain ⟨j, hj⟩ := hi
  exact ((hA i).eigenvalues₀_antitone le_top).trans_lt hj

/-- If `c` and `-c` lie in the limiting spectral support and the Euclidean operator norms are
eventually below every `r > c`, the largest eigenvalues converge to `c` and the smallest
eigenvalues converge to `-c`. -/
theorem eigenvalues₀_bot_and_top_of_eventually_l2_opNorm_lt
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ))
    {c : ℝ} (hc : c ∈ (μ : Measure ℝ).support) (hc' : -c ∈ (μ : Measure ℝ).support)
    (hnorm : ∀ r > c, ∀ᶠ i in l, ‖A i‖ < r) :
    Tendsto (fun i ↦ (hA i).eigenvalues₀ ⊥) l (𝓝 c) ∧
      Tendsto (fun i ↦ (hA i).eigenvalues₀ ⊤) l (𝓝 (-c)) := by
  refine ⟨h.eigenvalues₀_bot_of_eventually_lt hc fun r hr ↦ (hnorm r hr).mono fun i hi ↦
      (Real.le_norm_self _).trans_lt (((hA i).norm_eigenvalues₀_le_l2_opNorm ⊥).trans_lt hi),
    h.eigenvalues₀_top_of_eventually_gt hc' fun r hr ↦
      (hnorm (-r) (by linarith)).mono fun i hi ↦ ?_⟩
  have h' := ((hA i).norm_eigenvalues₀_le_l2_opNorm ⊤).trans_lt hi
  simpa only [neg_neg, Real.norm_eq_abs] using (neg_lt_neg h').trans_le (neg_abs_le _)

end Filter.Tendsto
