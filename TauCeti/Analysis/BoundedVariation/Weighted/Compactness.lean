/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
public import TauCeti.Analysis.BoundedVariation.Compactness
public import TauCeti.Probability.Distributions.Gaussian.Density
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Compactness for sets of bounded weighted perimeter

Let `W` be a `C¹` weight on a finite-dimensional real inner product space `E` whose measure
`μ = e^{−W} · volume` is finite. Every sequence of Lebesgue-measurable sets `U k` with
`sup_k P_μ(U k) < ∞` has a subsequence whose indicators converge in `L¹(μ)` to the indicator of a
measurable set `U`: `μ(U (φ j) ∆ U) → 0`
(`TauCeti.exists_subseq_tendsto_withDensity_symmDiff_of_weightedPerimeter_le`). For the
Gaussian weight, `μ` is the standard Gaussian measure
(`TauCeti.withDensity_exp_neg_gaussianWeight`), so sequences of bounded Gaussian perimeter have
subsequences converging in `L¹(γ)` (`TauCeti.exists_subseq_tendsto_stdGaussian_symmDiff`).

The route: the comparison of `V_μ` with the Euclidean variation bounds the Euclidean perimeters
of the `U k` near every compact set, since `e^{−W}` is bounded below there, so the Euclidean
compactness theorem `TauCeti.exists_subseq_tendsto_measure_symmDiff_inter_of_perimeter_le` gives
a subsequence converging locally in measure. On a ball `e^{−W}` is bounded above, and the mass of
`μ` outside large balls is small since `μ` is finite, which upgrades local convergence to
convergence in `L¹(μ)`. Finiteness of `μ` is needed: for the weight `0` on `ℝ` the intervals
`(k, k + 1)` all have perimeter `2` and converge to `∅` locally in measure, but not in `L¹`.

## References

* A. Cianchi, N. Fusco, F. Maggi, A. Pratelli, *On the isoperimetric deficit in Gauss space*,
  Amer. J. Math. (2011).
* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter Metric
open scoped ENNReal NNReal Topology symmDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ}

/-- A sequence of sets of bounded weighted perimeter in the whole space has locally bounded
Euclidean perimeter. -/
private theorem exists_perimeter_le_of_weightedPerimeter_le (hW : ContDiff ℝ 1 W) {s : ℕ → Set E}
    (hs : ∀ n, NullMeasurableSet (s n)) {M : ℝ≥0} (hP : ∀ n, weightedPerimeter W ⊤ (s n) ≤ M)
    (K : Set E) (hK : IsCompact K) :
    ∃ U : Opens E, K ⊆ (U : Set E) ∧ ∃ M' : ℝ≥0, ∀ n, perimeter volume U (s n) ≤ M' := by
  let U : Opens E := ⟨thickening 1 K, isOpen_thickening⟩
  obtain ⟨m', hm', hm'W⟩ := hK.cthickening.exists_forall_le'
    (Real.continuous_exp.comp hW.continuous.neg).continuousOn fun x _ => Real.exp_pos (-W x)
  let m : ℝ≥0 := ⟨m', hm'.le⟩
  have hm0 : m ≠ 0 := NNReal.coe_ne_zero.1 hm'.ne'
  have hm (x : E) (hx : x ∈ U) : (m : ℝ) ≤ Real.exp (-W x) :=
    hm'W x (thickening_subset_cthickening 1 K hx)
  refine ⟨U, self_subset_thickening one_pos K, M / m, fun n => ?_⟩
  have hle : (m : ℝ≥0∞) * perimeter volume U (s n) ≤ M := by
    rw [perimeter_def]
    exact (mul_totalVariationOn_le_weightedVariation hW
      (locallyIntegrableOn_indicator_const ((hs n).mono Measure.restrict_le_self) 1) hm).trans
      ((weightedVariation_mono le_top).trans (weightedPerimeter_def (W := W) ▸ hP n))
  rw [ENNReal.coe_div hm0, ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.coe_ne_zero.2 hm0))
    (Or.inl ENNReal.coe_ne_top), mul_comm]
  exact hle

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The mass of a finite measure outside the closed ball of radius `n` about `0` tends to `0`. -/
private theorem tendsto_measure_compl_closedBall_nat (ν : Measure E) [IsFiniteMeasure ν] :
    Tendsto (fun n : ℕ => ν (closedBall (0 : E) n)ᶜ) atTop (𝓝 0) := by
  have hempty : (⋂ n : ℕ, (closedBall (0 : E) n)ᶜ) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact mem_iInter.1 hx n (mem_closedBall_zero_iff.2 hn)
  have := tendsto_measure_iInter_atTop (μ := ν) (s := fun n : ℕ => (closedBall (0 : E) n)ᶜ)
    (fun n : ℕ => isClosed_closedBall.isOpen_compl.measurableSet.nullMeasurableSet)
    (fun _ _ h => compl_subset_compl.2 (closedBall_subset_closedBall (Nat.cast_le.2 h)))
    ⟨0, measure_ne_top _ _⟩
  rwa [hempty, measure_empty] at this

/-- **Compactness for bounded weighted perimeter.** Let `W` be a `C¹` weight whose measure
`μ = e^{−W} · volume` is finite. Every sequence of null-measurable sets `s n` with weighted
perimeters `P_μ(s n) ≤ M` has a subsequence converging in `L¹(μ)` to a measurable set `t`:
`μ(s (φ j) ∆ t) → 0`. -/
theorem exists_subseq_tendsto_withDensity_symmDiff_of_weightedPerimeter_le
    (hW : ContDiff ℝ 1 W)
    [IsFiniteMeasure (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-W x)))]
    {s : ℕ → Set E} (hs : ∀ n, NullMeasurableSet (s n)) {M : ℝ≥0}
    (hP : ∀ n, weightedPerimeter W ⊤ (s n) ≤ M) :
    ∃ t, MeasurableSet t ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-W x)))
        (s (φ j) ∆ t)) atTop (𝓝 0) := by
  set ν := volume.withDensity fun x => ENNReal.ofReal (Real.exp (-W x))
  obtain ⟨t, ht, φ, hφ, hloc⟩ := exists_subseq_tendsto_measure_symmDiff_inter_of_perimeter_le
    (μ := volume) (Ω := ⊤) (s := s) hs fun K hK _ => by
      obtain ⟨U, hKU, M', hM'⟩ := exists_perimeter_le_of_weightedPerimeter_le hW hs hP K hK
      exact ⟨U, hKU, le_top, M', hM'⟩
  refine ⟨t, ht, φ, hφ, ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_⟩
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1 (tendsto_measure_compl_closedBall_nat ν)
    (ε / 2) hε2).exists
  set K := closedBall (0 : E) n
  have hK : IsCompact K := isCompact_closedBall 0 n
  -- `e^{−W}` is bounded above on `K`.
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    (Real.continuous_exp.comp hW.continuous.neg).continuousOn
  have hνK (A : Set E) : ν (A ∩ K) ≤ ENNReal.ofReal C * volume (A ∩ K) := by
    rw [withDensity_apply', ← setLIntegral_const]
    refine lintegral_mono_ae (ae_restrict_of_ae_restrict_of_subset inter_subset_right
      (ae_restrict_of_forall_mem measurableSet_closedBall fun x hx => ?_))
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hC x hx))
  have hlim : Tendsto (fun j => ENNReal.ofReal C * volume ((s (φ j) ∆ t) ∩ K)) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul (hloc K hK (by simp)) (Or.inr ENNReal.ofReal_ne_top)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hlim (ε / 2) hε2] with j hj
  calc ν (s (φ j) ∆ t) ≤ ν ((s (φ j) ∆ t) ∩ K) + ν ((s (φ j) ∆ t) \ K) :=
        measure_le_inter_add_sdiff _ _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add ((hνK _).trans hj)
        ((measure_mono fun _ (hx : _ ∈ _ \ K) => hx.2).trans hn)
    _ = ε := ENNReal.add_halves ε

/-- The measure of the Gaussian weight is the standard Gaussian measure. -/
theorem withDensity_exp_neg_gaussianWeight :
    (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-gaussianWeight E x))) =
      ProbabilityTheory.stdGaussian E := by
  rw [Probability.stdGaussian_eq_withDensity_norm]
  congr 1 with x
  congr 1
  rw [gaussianWeight_def, neg_add, Real.exp_add, mul_comm, Real.rpow_def_of_pos (by positivity)]
  congr 2
  · ring
  · ring

/-- **Compactness for bounded Gaussian perimeter.** Every sequence of null-measurable sets with
Gaussian perimeters `P_γ(s n) ≤ M` has a subsequence converging in `L¹(γ)` to a measurable set
`t`: `γ(s (φ j) ∆ t) → 0`. -/
theorem exists_subseq_tendsto_stdGaussian_symmDiff {s : ℕ → Set E}
    (hs : ∀ n, NullMeasurableSet (s n)) {M : ℝ≥0} (hP : ∀ n, gaussianPerimeter (s n) ≤ M) :
    ∃ t, MeasurableSet t ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun j => ProbabilityTheory.stdGaussian E (s (φ j) ∆ t)) atTop (𝓝 0) := by
  have : IsFiniteMeasure
      (volume.withDensity fun x => ENNReal.ofReal (Real.exp (-gaussianWeight E x))) := by
    rw [withDensity_exp_neg_gaussianWeight]
    infer_instance
  simpa only [withDensity_exp_neg_gaussianWeight] using
    exists_subseq_tendsto_withDensity_symmDiff_of_weightedPerimeter_le contDiff_gaussianWeight hs
      fun n => gaussianPerimeter_def (s := s n) ▸ hP n

end TauCeti
