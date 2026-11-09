/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Basic
public import TauCeti.MeasureTheory.Measure.NNReal

import TauCeti.Probability.Distributions.Poisson.SmallRate
import Mathlib.Order.Interval.Set.Union

/-!
# Simplicity of homogeneous temporal Poisson random measures

A Poisson random measure on the half-line with intensity `r • nnvolume` almost surely
has mass at most one at every location, simultaneously. This is the simplicity needed
when passing between the random measure and its ordered event times. The result includes
rate zero and requires no prior integrality, local finiteness, or simplicity assumption
on the realizations.

The assertion is not obtained by intersecting the individual full-measure events at
uncountably many times. On each bounded interval, a multiple point belongs to a cell
with at least two occurrences at every equal-mesh subdivision. The Poisson factorial-
moment bound makes the probability of any such cell tend to zero. Outer measures
handle the possibly nonmeasurable event that a multiple point exists.

See G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University
Press, 2018, Chapters 6–7. The subdivision argument also parallels the existing
`ae_count_le_add_one_of_small_time` for natural-valued count processes; here it works
directly on measures without first choosing natural-valued versions of all counts.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {N : Ω → Measure ℝ≥0} {r : ℝ≥0}

private theorem measureReal_exists_multiple_singleton_Ioc_le
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume))
    (b : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
    P.real {ω | ∃ t ∈ Ioc 0 b, 1 < N ω {t}} ≤ (r * b : ℝ≥0) ^ 2 / (2 * n) := by
  let := h.isProbabilityMeasure
  let δ := b / (n : ℝ≥0)
  let B (k : ℕ) := {ω | 1 < N ω (Ioc ((k : ℝ≥0) * δ) ((k : ℝ≥0) * δ + δ))}
  have hcover : {ω | ∃ t ∈ Ioc 0 b, 1 < N ω {t}} ⊆
      ⋃ k ∈ Finset.range n, B k := by
    rintro ω ⟨t, ht, hmass⟩
    have ht' : t ∈ Ioc ((0 : ℝ≥0) * δ) ((n : ℝ≥0) * δ) := by
      simpa [δ, hn, mul_div_cancel₀] using ht
    obtain ⟨k, hk, hkt⟩ := mem_iUnion₂.mp (Ioc_subset_biUnion_Ioc n
      (fun k ↦ (k : ℝ≥0) * δ) (by simpa using ht'))
    refine mem_iUnion₂.mpr ⟨k, hk, ?_⟩
    apply hmass.trans_le (measure_mono (singleton_subset_iff.mpr ?_))
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hkt
  have hprob (k : ℕ) : P.real (B k) =
      (poissonMeasure (r * δ)).real (Ici 2) := by
    have hrate : ((r : ℝ≥0∞) • nnvolume)
        (Ioc ((k : ℝ≥0) * δ) ((k : ℝ≥0) * δ + δ)) = (r * δ : ℝ≥0) := by
      simp only [smul_apply, nnvolume_Ioc, add_tsub_cancel_left,
        smul_eq_mul, ENNReal.coe_mul]
    have hlaw := h.hasLaw measurableSet_Ioc (by rw [hrate]; exact ENNReal.coe_lt_top)
    rw [hrate, ENNReal.toNNReal_coe] at hlaw
    rw [hlaw.measureReal_eq measurableSet_Ioi,
      map_measureReal_apply_of_aemeasurable Measurable.of_discrete.aemeasurable
        (s := {x : ℝ≥0∞ | 1 < x}) measurableSet_Ioi]
    congr 1
    ext j
    simp only [mem_preimage, mem_ofPred_eq, mem_Ici]
    norm_cast
  calc
    _ ≤ P.real (⋃ k ∈ Finset.range n, B k) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.range n, P.real (B k) := measureReal_biUnion_finset_le _ _
    _ = (n : ℝ) * (poissonMeasure (r * δ)).real (Ici 2) := by simp [hprob]
    _ ≤ (n : ℝ) * ((r * δ : ℝ≥0) : ℝ) ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_left (poissonMeasure_real_Ici_two_le (r * δ))
        (Nat.cast_nonneg (α := ℝ) n)
      simpa only [mul_div_assoc] using this
    _ = _ := by
      simp only [δ, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast]
      field_simp

/-- A homogeneous Poisson random measure on the half-line has no multiple points almost
surely. The bound holds for every location on one event of full measure, including at zero,
and also at rate zero. No pathwise integrality or local finiteness hypothesis is needed. -/
theorem IsPoissonRandomMeasure.ae_forall_singleton_le_one
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, N ω {t} ≤ 1 := by
  let := h.isProbabilityMeasure
  have hnull (b : ℝ≥0) : P {ω | ∃ t ∈ Ioc 0 b, 1 < N ω {t}} = 0 := by
    rw [← measureReal_eq_zero_iff]
    apply le_antisymm _ measureReal_nonneg
    have hlim := tendsto_const_div_atTop_nhds_zero_nat (((r * b : ℝ≥0) : ℝ) ^ 2 / 2)
    refine ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
    simpa only [div_mul_eq_div_div, div_right_comm] using
      measureReal_exists_multiple_singleton_Ioc_le h b (by omega : n ≠ 0)
  have hae : ∀ᵐ ω ∂P, ∀ m : ℕ, ¬∃ t ∈ Ioc 0 (m + 1 : ℝ≥0), 1 < N ω {t} := by
    exact ae_all_iff.mpr fun m ↦ by simpa only [ae_iff, not_not] using hnull (m + 1)
  have hzero : ∀ᵐ ω ∂P, N ω {0} = 0 := by
    have hlaw := h.hasLaw (measurableSet_singleton 0) (by simp)
    have hlaw' : HasLaw (fun ω ↦ N ω {0}) (Measure.dirac 0) P := by
      simpa [poissonMeasure_zero] using hlaw
    exact hlaw'.ae_eq_of_dirac
  filter_upwards [hae, hzero] with ω hω h0 t
  rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ t) with ht | ht
  · simp [← ht, h0]
  · obtain ⟨m, hm⟩ := exists_nat_gt t
    exact not_lt.mp fun hmass ↦ hω m ⟨t, ⟨ht, hm.le.trans (by simp)⟩, hmass⟩

end TauCeti.Probability
