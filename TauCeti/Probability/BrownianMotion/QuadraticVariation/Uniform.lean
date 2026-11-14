/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.PartitionMaximal
import TauCeti.Analysis.QuadraticSums
import TauCeti.MeasureTheory.Constructions.BorelSpace.RightContinuous
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Uniform convergence of Brownian quadratic sums

Squared-increment sums clipped at the observation time converge to elapsed time uniformly
in probability on each compact interval. This includes the unfinished cell, not just the
grid-point sums. The grids need not be nested, may repeat dates, and may have no intervals
when the horizon is zero. Only their used finite prefixes must be ordered.

The probability is stated directly for the event that the error exceeds a positive tolerance
at some time in the interval. The event is null-measurable, even for an uncompleted sample
space and a Brownian version with only almost-sure path continuity. No filtration is needed.
These are the uniform partition limits used in stochastic change-of-variables formulas.

The proof combines the maximal grid-point estimates in
`TauCeti.Probability.BrownianMotion.PartitionMaximal` with the deterministic unfinished-cell
estimate in `TauCeti.Analysis.QuadraticSums`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §1.5 and §3.3.
-/

public section

noncomputable section

open MeasureTheory Filter Finset Set
open scoped NNReal Topology ENNReal

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {a b : ℝ≥0} {N : ℕ → ℕ} {grid : ℕ → ℕ → ℝ≥0} {δ : ℕ → ℝ}

private theorem exists_subseq_tendstoUniformlyOn_quadraticSum_min
    (hB : IsBrownianReal B P) (ht : ∀ k, MonotoneOn (grid k) (Set.Iic (N k)))
    (ha : ∀ k, grid k 0 = a) (hb : ∀ k, grid k (N k) = b)
    (hδ : ∀ k, 0 ≤ δ k)
    (hmesh : ∀ k i, i < N k → (grid k (i + 1) : ℝ) - grid k i ≤ δ k)
    (hδlim : Tendsto δ atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P,
      TendstoUniformlyOn (fun k u ↦
        (∑ i ∈ range (N (ns k)),
          (B (min u (grid (ns k) (i + 1))) ω - B (min u (grid (ns k) i)) ω) ^ 2) -
            ((u : ℝ) - a)) (fun _ ↦ 0) atTop (Icc a b) := by
  have hprob := hB.toIsPreBrownianReal.tendstoInMeasure_partialSups_abs_quadraticSumSubTime
    ht (fun k ↦ (hb k).le) hmesh hδlim
  obtain ⟨ns, hns, hlim⟩ := hprob.exists_seq_tendsto_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hB.cont, hlim] with ω hc hω
  apply hc.continuousOn.tendstoUniformlyOn_sum_sq_min_sub_time
    (fun k ↦ ht (ns k)) (fun k ↦ ha (ns k)) (fun k ↦ hb (ns k))
    (fun k ↦ hδ (ns k)) (fun k ↦ hmesh (ns k)) (hδlim.comp hns.tendsto_atTop) hω
  intro k j hj
  rw [← ha (ns k), ← quadraticSumSubTime_eq_sum_sub]
  exact le_partialSups_of_le (fun j ω ↦ |quadraticSumSubTime B (grid (ns k)) j ω|) hj ω

private theorem nullMeasurableSet_exists_abs_quadraticSum_min_sub_time
    (hB : IsBrownianReal B P) (ht : ∀ k, MonotoneOn (grid k) (Set.Iic (N k)))
    (ha : ∀ k, grid k 0 = a) {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    NullMeasurableSet {ω | ∃ u ∈ Icc a b, ε <
      |(∑ i ∈ range (N k),
        (B (min u (grid k (i + 1))) ω - B (min u (grid k i)) ω) ^ 2) -
          ((u : ℝ) - a)|} P := by
  -- Freezing the elapsed-time correction below `a` makes the error zero there.
  let E k u ω := (∑ i ∈ range (N k),
    (B (min u (grid k (i + 1))) ω - B (min u (grid k i)) ω) ^ 2) -
      ((max a u : ℝ≥0) - a)
  let A k := {ω | ∃ u ∈ Icc a b, ε < |E k u ω|}
  have hE k u : AEMeasurable (E k u) P := by
    exact (Finset.aemeasurable_fun_sum _ (fun i _ ↦
      ((hB.aemeasurable _).sub (hB.aemeasurable _)).pow_const 2)).sub aemeasurable_const
  have hcE : ∀ᵐ ω ∂P, ∀ k, Continuous (fun u ↦ |E k u ω|) := by
    filter_upwards [hB.cont] with ω hω k
    dsimp [E]
    fun_prop
  have hA k : NullMeasurableSet (A k) P := by
    have hm := aemeasurable_iSup_le_ofReal (fun u ↦ by
      simpa only [Real.norm_eq_abs] using (hE k u).norm)
      (T := b) (hcE.mono fun ω hω t _ ↦ (hω k).continuousWithinAt)
    have heq : A k = {ω | ENNReal.ofReal ε < ⨆ u ≤ b, ENNReal.ofReal |E k u ω|} := by
      ext ω
      simp only [A, mem_ofPred_eq, lt_iSup_iff, ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le]
      constructor
      · rintro ⟨u, hu, h⟩
        exact ⟨u, hu.2, h⟩
      · rintro ⟨u, hub, h⟩
        have hau : a ≤ u := by
          by_contra hnot
          have hzero : E k u ω = 0 := by
            have hle i (hi : i < N k) : u ≤ grid k i :=
              (le_of_not_ge hnot).trans ((ha k).symm.le.trans
                (ht k (Nat.zero_le _) hi.le (Nat.zero_le _)))
            have hle' i (hi : i < N k) : u ≤ grid k (i + 1) :=
              (hle i hi).trans (ht k hi.le hi (Nat.le_succ i))
            simp only [E, NNReal.coe_max,
              max_eq_left (NNReal.coe_le_coe.mpr (le_of_not_ge hnot)), sub_self, sub_zero]
            apply sum_eq_zero
            intro i hi
            rw [min_eq_left (hle' i (Finset.mem_range.mp hi)),
              min_eq_left (hle i (Finset.mem_range.mp hi))]
            simp
          simp [hzero, not_lt_of_ge hε.le] at h
        exact ⟨u, ⟨hau, hub⟩, h⟩
    rw [heq]
    exact hm.nullMeasurable measurableSet_Ioi
  have htarget : A k = {ω | ∃ u ∈ Icc a b, ε <
      |(∑ i ∈ range (N k),
        (B (min u (grid k (i + 1))) ω - B (min u (grid k i)) ω) ^ 2) -
          ((u : ℝ) - a)|} := by
    ext ω
    exact exists_congr fun u ↦ and_congr_right fun hu ↦ by
      simp only [E, max_eq_right hu.1]
  rw [← htarget]
  exact hA k

/-- Brownian quadratic sums, including their terminal partial increment, converge uniformly
in probability to elapsed time on a compact interval along every deterministic vanishing-mesh
sequence. No nesting, strict ordering, or usual-filtration assumption is needed. -/
theorem tendsto_measure_exists_abs_quadraticSum_min_sub_time
    (hB : IsBrownianReal B P) (ht : ∀ k, MonotoneOn (grid k) (Set.Iic (N k)))
    (ha : ∀ k, grid k 0 = a) (hb : ∀ k, grid k (N k) = b)
    (hmesh : ∀ k i, i < N k → (grid k (i + 1) : ℝ) - grid k i ≤ δ k)
    (hδlim : Tendsto δ atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ∃ u ∈ Icc a b, ε <
      |(∑ i ∈ range (N k),
        (B (min u (grid k (i + 1))) ω - B (min u (grid k i)) ω) ^ 2) -
          ((u : ℝ) - a)|}) atTop (𝓝 0) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let A k := {ω | ∃ u ∈ Icc a b, ε <
    |(∑ i ∈ range (N k),
      (B (min u (grid k (i + 1))) ω - B (min u (grid k i)) ω) ^ 2) - ((u : ℝ) - a)|}
  have hA k : NullMeasurableSet (A k) P :=
    hB.nullMeasurableSet_exists_abs_quadraticSum_min_sub_time ht ha hε k
  -- Every subsequence has a further subsequence with almost-sure uniform convergence.
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, _, hlim⟩ := hB.exists_subseq_tendstoUniformlyOn_quadraticSum_min
    (fun k ↦ ht (ns k)) (fun k ↦ ha (ns k)) (fun k ↦ hb (ns k))
    (fun k ↦ le_max_right (δ (ns k)) 0)
    (fun k i hi ↦ (hmesh (ns k) i hi).trans (le_max_left _ _))
    (by simpa using (hδlim.comp hns).max (tendsto_const_nhds (x := (0 : ℝ))))
  refine ⟨ms, ?_⟩
  have heq := ae_all_iff.mpr (fun k ↦ (hA (ns (ms k))).toMeasurable_ae_eq)
  have hnot : ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      ω ∈ toMeasurable P (A (ns (ms k))) ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hlim, heq] with ω hω heqω
    have hsmall := (Metric.tendstoUniformlyOn_iff.mp hω) ε hε
    filter_upwards [hsmall] with k hk
    rw [heqω k]
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨u, hu, herr⟩
    have hk' := hk u hu
    simp only [Real.dist_eq, zero_sub, abs_neg] at hk'
    exact (hk'.trans herr).false
  have hlim' := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    MeasurableSet.empty (fun k ↦ measurableSet_toMeasurable P _) hnot
  simpa only [measure_empty, measure_toMeasurable] using hlim'

end ProbabilityTheory.IsBrownianReal
