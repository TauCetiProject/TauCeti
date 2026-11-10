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
import Mathlib.MeasureTheory.Function.Floor

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
on measures, using natural-valued versions only for the countably many mesh cells.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {N : Ω → Measure ℝ≥0} {r : ℝ≥0}

private theorem measure_exists_multiple_singleton_Ioc_eq_zero
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) (b : ℝ≥0) :
    P {ω | ∃ t ∈ Ioc 0 b, 1 < N ω {t}} = 0 := by
  let := h.isProbabilityMeasure
  let δ (n : ℕ) := b / (n : ℝ≥0)
  let C (n k : ℕ) := Ioc ((k : ℝ≥0) * δ n) ((k : ℝ≥0) * δ n + δ n)
  -- Recover natural-valued cell counts to apply the existing small-rate limit.
  let count (x : ℝ≥0∞) := ⌊x.toNNReal⌋₊
  have hm : Measurable count := Nat.measurable_floor.comp ENNReal.measurable_toNNReal
  have hlaw (n k : ℕ) : HasLaw (fun ω ↦ N ω (C n k))
      ((poissonMeasure (r * b / n)).map (Nat.cast : ℕ → ℝ≥0∞)) P := by
    have hrate : ((r : ℝ≥0∞) • nnvolume) (C n k) = (r * b / n : ℝ≥0) := by
      simp only [C, smul_apply, nnvolume_Ioc, add_tsub_cancel_left,
        smul_eq_mul, ← ENNReal.coe_mul]
      simp only [δ, mul_div_assoc]
    simpa only [hrate, ENNReal.toNNReal_coe] using
      h.hasLaw (A := C n k) measurableSet_Ioc (by rw [hrate]; exact ENNReal.coe_lt_top)
  let X (n : ℕ) (i : Fin n) (ω : Ω) := count (N ω (C n i))
  have hX (n : ℕ) (i : Fin n) : HasLaw (X n i) (poissonMeasure (r * b / n)) P := by
    have hinv : HasLaw count (poissonMeasure (r * b / n))
        ((poissonMeasure (r * b / n)).map (Nat.cast : ℕ → ℝ≥0∞)) := by
      refine ⟨hm.aemeasurable, ?_⟩
      rw [Measure.map_map hm Measurable.of_discrete]
      simp [count, Function.comp_def]
    exact hinv.comp (hlaw n i)
  have hcount (n : ℕ) : ∀ᵐ ω ∂P, ∀ i : Fin n, (X n i ω : ℝ≥0∞) = N ω (C n i) := by
    refine ae_all_iff.mpr fun i ↦
      ((hlaw n i).ae_iff (p := fun x ↦ (count x : ℝ≥0∞) = x) (by fun_prop)).mpr ?_
    apply (ae_map_iff Measurable.of_discrete.aemeasurable
      (measurableSet_eq_fun (f := fun x : ℝ≥0∞ ↦ (count x : ℝ≥0∞))
        (by fun_prop) measurable_id)).mpr
    exact ae_of_all _ fun k ↦ by simp [count]
  rw [← measureReal_eq_zero_iff]
  apply le_antisymm _ measureReal_nonneg
  refine ge_of_tendsto (tendsto_measureReal_exists_two_le_of_hasLaw_poissonMeasure
    (r * b) hX) (eventually_atTop.2 ⟨1, fun n hn ↦ ?_⟩)
  -- On the full-measure count-recovery event, a multiple point forces a bad mesh cell.
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hcount n] with ω hω
  rintro ⟨t, ht, hmass⟩
  have ht' : t ∈ Ioc ((0 : ℝ≥0) * δ n) ((n : ℝ≥0) * δ n) := by
    simpa [δ, mul_div_cancel₀, Nat.ne_zero_of_lt hn] using ht
  obtain ⟨k, hk, hkt⟩ := mem_iUnion₂.mp (Ioc_subset_biUnion_Ioc n
    (fun k ↦ (k : ℝ≥0) * δ n) (by simpa using ht'))
  have hle : N ω {t} ≤ N ω (C n k) := by
    apply measure_mono (singleton_subset_iff.mpr ?_)
    simpa only [C, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hkt
  refine ⟨⟨k, Finset.mem_range.mp hk⟩, ?_⟩
  have : (1 : ℝ≥0∞) < X n ⟨k, Finset.mem_range.mp hk⟩ ω := by
    simpa only [hω] using hmass.trans_le hle
  exact Nat.succ_le_of_lt (by exact_mod_cast this)

/-- A homogeneous Poisson random measure on the half-line has no multiple points almost
surely. The bound holds for every location on one event of full measure, including at zero,
and also at rate zero. No pathwise integrality or local finiteness hypothesis is needed. -/
theorem IsPoissonRandomMeasure.ae_forall_singleton_le_one
    (h : IsPoissonRandomMeasure P N ((r : ℝ≥0∞) • nnvolume)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, N ω {t} ≤ 1 := by
  let := h.isProbabilityMeasure
  have hae : ∀ᵐ ω ∂P, ∀ m : ℕ, ¬∃ t ∈ Ioc 0 (m + 1 : ℝ≥0), 1 < N ω {t} := by
    exact ae_all_iff.mpr fun m ↦ by
      simpa only [ae_iff, not_not] using measure_exists_multiple_singleton_Ioc_eq_zero h (m + 1)
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
