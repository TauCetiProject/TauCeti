/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.Basic
public import TauCeti.MeasureTheory.Measure.IntegerValued.Basic
public import TauCeti.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Reconstruction from ordered occurrence times

A locally finite integer-valued measure on the half-line is the sum of the Dirac
occurrences at its finite `Measure.occurrenceTime`s. Infinite entries contribute the
zero measure, not a spurious occurrence at zero. The times tend to infinity, even
when the total mass is finite, and retain repeated locations when there are multiple
occurrences. An atom at zero is allowed.

Consequently ordered occurrence times determine both a counting measure and its law.
The law-transfer result allows different sample spaces and requires local finiteness
and integrality only almost surely. This connects temporal point-measure laws to
arrival-sequence laws without choosing an arbitrary enumeration of atoms.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge
  University Press, 2018, Chapters 2 and 7.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

/-- The measure with one occurrence at every finite entry of a time sequence.
Repeated entries retain their multiplicity, including at zero; infinite entries
contribute no mass. No ordering or nonaccumulation hypothesis is required. -/
noncomputable def occurrenceTimeMeasure (t : ℕ → ℝ≥0∞) : Measure ℝ≥0 :=
  Measure.sum fun n => if t n = ∞ then 0 else Measure.dirac (t n).toNNReal

/-- Expand the measure associated to a sequence as a sum of its finite occurrences. -/
theorem occurrenceTimeMeasure_def (t : ℕ → ℝ≥0∞) :
    occurrenceTimeMeasure t =
      Measure.sum (fun n => if t n = ∞ then 0 else Measure.dirac (t n).toNNReal) := (rfl)

/-- Forming the measure of finite occurrences is measurable in the entire time sequence. -/
@[fun_prop]
theorem measurable_occurrenceTimeMeasure : Measurable occurrenceTimeMeasure := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [occurrenceTimeMeasure_def, Measure.sum_apply _ hA]
  have hm (n : ℕ) : Measurable (fun t : ℕ → ℝ≥0∞ =>
      if t n = ∞ then (0 : Measure ℝ≥0) else Measure.dirac (t n).toNNReal) :=
    Measurable.ite (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)
      measurable_const (Measure.measurable_dirac.comp
        (ENNReal.measurable_toNNReal.comp (measurable_pi_apply n)))
  exact Measurable.tsum fun n => (Measure.measurable_coe hA).comp (hm n)

open Classical in
/-- Evaluation counts finite occurrences in the set, with multiplicity. -/
theorem occurrenceTimeMeasure_apply (t : ℕ → ℝ≥0∞) (s : Set ℝ≥0) :
    occurrenceTimeMeasure t s =
      ∑' n, if t n ≠ ∞ ∧ (t n).toNNReal ∈ s then (1 : ℝ≥0∞) else 0 := by
  classical
  rw [occurrenceTimeMeasure_def, Measure.sum_apply_of_countable]
  refine tsum_congr fun n => ?_
  by_cases hn : t n = ∞ <;> simp [hn, Measure.dirac_apply, Set.indicator_apply]

/-- The cumulative mass counts all entries at or before the finite endpoint. -/
@[simp]
theorem occurrenceTimeMeasure_Iic (t : ℕ → ℝ≥0∞) (x : ℝ≥0) :
    occurrenceTimeMeasure t (Iic x) = ∑' n, if t n ≤ x then (1 : ℝ≥0∞) else 0 := by
  classical
  rw [occurrenceTimeMeasure_apply]
  refine tsum_congr fun n => ?_
  by_cases hn : t n = ∞
  · simp [hn]
  · have hle : (t n).toNNReal ≤ x ↔ t n ≤ x := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hn]
    simp [hn, hle]

/-- Integration sums the test function over finite occurrences only. -/
@[simp]
theorem lintegral_occurrenceTimeMeasure (t : ℕ → ℝ≥0∞) (f : ℝ≥0 → ℝ≥0∞) :
    ∫⁻ x, f x ∂occurrenceTimeMeasure t = ∑' n, if t n = ∞ then 0 else f (t n).toNNReal := by
  rw [occurrenceTimeMeasure_def, lintegral_sum_measure]
  refine tsum_congr fun n => ?_
  split_ifs <;> simp

/-- Every sequence of occurrences gives an integer-valued measure, even with accumulation. -/
@[simp]
theorem isIntegerValued_occurrenceTimeMeasure (t : ℕ → ℝ≥0∞) :
    (occurrenceTimeMeasure t).IsIntegerValued := by
  rw [occurrenceTimeMeasure_def]
  exact Measure.IsIntegerValued.sum fun n => by
    split_ifs <;> simp

/-- Escape to infinity ensures that every bounded window contains finitely many occurrences. -/
theorem isLocallyFiniteMeasure_occurrenceTimeMeasure {t : ℕ → ℝ≥0∞}
    (ht : Tendsto t atTop (𝓝 ∞)) : IsLocallyFiniteMeasure (occurrenceTimeMeasure t) := by
  classical
  refine ⟨fun x => ⟨Iio (x + 1), Iio_mem_nhds (lt_add_one x), ?_⟩⟩
  apply (measure_mono Iio_subset_Iic_self).trans_lt
  rw [occurrenceTimeMeasure_Iic]
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (ht.eventually (eventually_gt_nhds (ENNReal.coe_lt_top (r := x + 1))))
  rw [tsum_eq_sum (s := Finset.range N) (fun n hn =>
    ite_eq_right (not_le_of_gt (hN n (by simpa using hn))))]
  exact ENNReal.sum_lt_top.mpr fun n _ => by split_ifs <;> simp

private theorem natCast_succ_le_occurrenceTimeMeasure_Iic_iff {t : ℕ → ℝ≥0∞}
    (hmono : Monotone t) (n : ℕ) (x : ℝ≥0) :
    (n + 1 : ℝ≥0∞) ≤ occurrenceTimeMeasure t (Iic x) ↔ t n ≤ x := by
  classical
  rw [occurrenceTimeMeasure_Iic]
  constructor
  · intro h
    by_contra hn
    have hsum : (∑' k, if t k ≤ x then (1 : ℝ≥0∞) else 0) ≤ n := by
      rw [tsum_eq_sum (s := Finset.range n) (fun k hk =>
        ite_eq_right (fun h => hn ((hmono (by simpa using hk)).trans h)))]
      exact (Finset.sum_le_card_nsmul _ _ 1 (fun k _ => by split_ifs <;> simp)).trans
        (by simp)
    have hlt : (n : ℝ≥0∞) < n + 1 := by exact_mod_cast Nat.lt_succ_self n
    exact hlt.not_ge (h.trans hsum)
  · intro hn
    calc
      (n + 1 : ℝ≥0∞) = ∑ _k ∈ Finset.range (n + 1), (1 : ℝ≥0∞) := by simp
      _ = ∑ k ∈ Finset.range (n + 1), if t k ≤ x then (1 : ℝ≥0∞) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [ite_eq_left ((hmono (Nat.le_of_lt_succ (Finset.mem_range.1 hk))).trans hn)]
      _ ≤ ∑' k, if t k ≤ x then (1 : ℝ≥0∞) else 0 := sum_le_tsum _

/-- Reading a monotone sequence's occurrences recovers the sequence, including infinite
entries. No nonaccumulation hypothesis is needed for this inverse direction. -/
@[simp]
theorem occurrenceTime_occurrenceTimeMeasure {t : ℕ → ℝ≥0∞} (hmono : Monotone t) :
    (occurrenceTimeMeasure t).occurrenceTime = t := by
  funext n
  apply le_antisymm
  · by_cases hn : t n = ∞
    · simp [hn]
    · rw [← ENNReal.coe_toNNReal hn]
      apply Measure.occurrenceTime_le_of_le
      exact (natCast_succ_le_occurrenceTimeMeasure_Iic_iff hmono n _).2
        (le_of_eq (ENNReal.coe_toNNReal hn).symm)
  · rw [Measure.occurrenceTime_def]
    exact le_iInf fun x => le_iInf fun hx =>
      (natCast_succ_le_occurrenceTimeMeasure_Iic_iff hmono n x).1 hx

/-- Local finiteness is equivalent to escape to infinity, without an ordering hypothesis. -/
theorem isLocallyFiniteMeasure_occurrenceTimeMeasure_iff {t : ℕ → ℝ≥0∞} :
    IsLocallyFiniteMeasure (occurrenceTimeMeasure t) ↔ Tendsto t atTop (𝓝 ∞) := by
  classical
  constructor
  · intro hloc
    refine ENNReal.tendsto_nhds_top_iff_nnreal.2 fun x => ?_
    have hsum : (∑' n, if t n ≤ x then (1 : ℝ≥0∞) else 0) ≠ ∞ := by
      rw [← occurrenceTimeMeasure_Iic]
      exact (measure_Iic_lt_top (μ := occurrenceTimeMeasure t)).ne
    have hfinite : {n | t n ≤ x}.Finite := by
      refine (ENNReal.finite_const_le_of_tsum_ne_top hsum one_ne_zero).subset ?_
      intro n hn
      simp only [mem_ofPred_eq] at hn ⊢
      simp [hn]
    filter_upwards [Filter.atTop_le_cofinite hfinite.compl_mem_cofinite] with n hn
    exact lt_of_not_ge hn
  · exact isLocallyFiniteMeasure_occurrenceTimeMeasure

end TauCeti.Probability

open TauCeti.Probability

namespace MeasureTheory.Measure

variable {μ ν : Measure ℝ≥0}

/-- The cumulative mass counts the ordered occurrence times, including the right endpoint
and all occurrences at zero. -/
theorem IsIntegerValued.apply_Iic_eq_tsum_occurrenceTime [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) (t : ℝ≥0) :
    μ (Iic t) = ∑' n : ℕ, if μ.occurrenceTime n ≤ t then (1 : ℝ≥0∞) else 0 := by
  classical
  obtain ⟨k, hk⟩ := hμ.exists_eq_natCast measurableSet_Iic (measure_Iic_lt_top (μ := μ))
  have heq (n : ℕ) : μ.occurrenceTime n ≤ t ↔ n < k := by
    rw [occurrenceTime_le_iff, hk]
    exact_mod_cast Nat.succ_le_iff
  simp_rw [heq]
  rw [tsum_eq_sum (s := Finset.range k) (fun n hn => by simp_all)]
  simp [hk, ← Finset.mem_range]

/-- Every locally finite counting measure is reconstructed from its ordered finite
occurrence times. Multiplicities are retained, and infinite times contribute no mass. -/
theorem IsIntegerValued.eq_occurrenceTimeMeasure [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) : μ = occurrenceTimeMeasure μ.occurrenceTime := by
  classical
  apply Measure.ext_of_Iic' μ _ (fun _ => (measure_Iic_lt_top (μ := μ)).ne)
  intro t
  rw [hμ.apply_Iic_eq_tsum_occurrenceTime, occurrenceTimeMeasure_Iic]

/-- On locally finite counting measures, equality of ordered occurrence sequences is
equivalent to equality of measures. The integrality assumption is essential. -/
@[simp]
theorem IsIntegerValued.occurrenceTime_inj [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] (hμ : μ.IsIntegerValued) (hν : ν.IsIntegerValued) :
    μ.occurrenceTime = ν.occurrenceTime ↔ μ = ν := by
  constructor
  · intro h
    rw [hμ.eq_occurrenceTimeMeasure, hν.eq_occurrenceTimeMeasure, h]
  · rintro rfl
    rfl

end MeasureTheory.Measure

namespace ProbabilityTheory.IdentDistrib

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} {N : Ω → Measure ℝ≥0} {N' : Ω' → Measure ℝ≥0}

private theorem occurrenceTimeMeasure_occurrenceTime_ae_eq
    (hN : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (N ω) ∧ (N ω).IsIntegerValued) :
    occurrenceTimeMeasure ∘ (fun ω => (N ω).occurrenceTime) =ᵐ[P] N := by
  filter_upwards [hN] with ω hω
  have hloc : IsLocallyFiniteMeasure (N ω) := hω.1
  exact hω.2.eq_occurrenceTimeMeasure.symm

/-- Equality in law of the whole ordered occurrence sequence implies equality in law of
the temporal counting measures. Local finiteness and integrality are required only on
full-measure events. Neither simplicity nor infinitely many occurrences is assumed. -/
theorem of_occurrenceTime
    (h : IdentDistrib (fun ω => (N ω).occurrenceTime)
      (fun ω => (N' ω).occurrenceTime) P P')
    (hN : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (N ω) ∧ (N ω).IsIntegerValued)
    (hN' : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (N' ω) ∧ (N' ω).IsIntegerValued) :
    IdentDistrib N N' P P' := by
  have hRlaw := h.comp measurable_occurrenceTimeMeasure
  exact (IdentDistrib.of_ae_eq hRlaw.aemeasurable_fst
    (occurrenceTimeMeasure_occurrenceTime_ae_eq hN)).symm.trans
      (hRlaw.trans (IdentDistrib.of_ae_eq hRlaw.aemeasurable_snd
        (occurrenceTimeMeasure_occurrenceTime_ae_eq hN')))

end ProbabilityTheory.IdentDistrib
