/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Extreme eigenvalues and weak spectral limits

Any open interval meeting the support of the weak limit of empirical spectral measures
eventually contains an eigenvalue. In particular, if both endpoints of a symmetric interval
belong to the support, an asymptotic operator-norm bound by the radius gives convergence
of the two extreme eigenvalues to the endpoints.
-/

public section

open Filter MeasureTheory Set
open scoped Topology Matrix.Norms.L2Operator

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

/-- When both `±c` are in the support of the limiting spectral measure, an asymptotic
operator-norm bound by `c` forces the largest eigenvalue to tend to `c` and the smallest
to tend to `-c`. -/
theorem tendsto_extreme_eigenvalues₀_of_tendsto_spectralMeasure
    (h : Tendsto (fun i ↦ (A i).spectralMeasure (hA i)) l (𝓝 μ))
    {c : ℝ} (hplus : c ∈ (μ : Measure ℝ).support) (hminus : -c ∈ (μ : Measure ℝ).support)
    (hnorm : ∀ r > c, ∀ᶠ i in l, ‖A i‖ < r) :
    Tendsto (fun i ↦ (hA i).eigenvalues₀ 0) l (𝓝 c) ∧
      Tendsto (fun i ↦ (hA i).eigenvalues₀ (Fin.last (Fintype.card (m i) - 1) |>.cast
        (Nat.sub_add_cancel Fintype.card_pos))) l (𝓝 (-c)) := by
  have hB (i : ι) (j : Fin (Fintype.card (m i))) : ‖(hA i).eigenvalues₀ j‖ ≤ ‖A i‖ := by
    rw [(hA i).l2_opNorm_eq_norm_eigenvalues]
    let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (m i)))
    simpa only [IsHermitian.eigenvalues, e, Equiv.symm_apply_apply] using
      norm_le_pi_norm (hA i).eigenvalues (e j)
  constructor
  · refine tendsto_order.2 ⟨fun r hr ↦ ?_, fun r hr ↦ ?_⟩
    · have hpos := (Measure.mem_support_iff_forall c).1 hplus _ (Ioi_mem_nhds hr)
      have he := eventually_exists_eigenvalues₀_mem_of_tendsto_spectralMeasure h isOpen_Ioi hpos
      filter_upwards [he] with i hi
      obtain ⟨j, hj⟩ := hi
      exact hj.trans_le ((hA i).eigenvalues₀_antitone (Fin.zero_le j))
    · exact (hnorm _ hr).mono fun i hi ↦ (Real.le_norm_self _).trans_lt ((hB i _).trans_lt hi)
  · refine tendsto_order.2 ⟨fun r hr ↦ ?_, fun r hr ↦ ?_⟩
    · filter_upwards [hnorm (-r) (by linarith)] with i hi
      have hb := (hB i ((Fin.last (Fintype.card (m i) - 1)).cast
        (Nat.sub_add_cancel Fintype.card_pos))).trans_lt hi
      simpa only [neg_neg, Real.norm_eq_abs] using (neg_lt_neg hb).trans_le (neg_abs_le _)
    · have hpos := (Measure.mem_support_iff_forall (-c)).1 hminus _ (Iio_mem_nhds hr)
      have he := eventually_exists_eigenvalues₀_mem_of_tendsto_spectralMeasure h isOpen_Iio hpos
      filter_upwards [he] with i hi
      obtain ⟨j, hj⟩ := hi
      exact ((hA i).eigenvalues₀_antitone (by
        simp only [Fin.le_iff_val_le_val, Fin.val_cast, Fin.val_last]
        omega)).trans_lt hj

end Matrix
