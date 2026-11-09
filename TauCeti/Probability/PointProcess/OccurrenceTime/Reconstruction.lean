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
theorem IsIntegerValued.eq_sum_dirac_occurrenceTime [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) :
    μ = Measure.sum (fun n : ℕ => if μ.occurrenceTime n = ∞ then 0
      else Measure.dirac (μ.occurrenceTime n).toNNReal) := by
  classical
  apply Measure.ext_of_Iic' μ _ (fun _ => (measure_Iic_lt_top (μ := μ)).ne)
  intro t
  rw [hμ.apply_Iic_eq_tsum_occurrenceTime, Measure.sum_apply _ measurableSet_Iic]
  apply tsum_congr
  intro n
  by_cases hn : μ.occurrenceTime n = ∞
  · simp [hn]
  · have hle : (μ.occurrenceTime n).toNNReal ≤ t ↔ μ.occurrenceTime n ≤ t := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hn]
    simp only [hn, ↓reduceIte, Measure.dirac_apply' _ measurableSet_Iic,
      Set.indicator_apply, mem_Iic, Pi.one_apply, hle]

/-- On locally finite counting measures, equality of ordered occurrence sequences is
equivalent to equality of measures. The integrality assumption is essential. -/
@[simp]
theorem IsIntegerValued.occurrenceTime_eq_iff [IsLocallyFiniteMeasure μ]
    [IsLocallyFiniteMeasure ν] (hμ : μ.IsIntegerValued) (hν : ν.IsIntegerValued) :
    μ.occurrenceTime = ν.occurrenceTime ↔ μ = ν := by
  constructor
  · intro h
    rw [hμ.eq_sum_dirac_occurrenceTime, hν.eq_sum_dirac_occurrenceTime, h]
  · rintro rfl
    rfl

end MeasureTheory.Measure

namespace ProbabilityTheory.IdentDistrib

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} {N : Ω → Measure ℝ≥0} {N' : Ω' → Measure ℝ≥0}

/-- Equality in law of the whole ordered occurrence sequence implies equality in law of
the temporal counting measures. Local finiteness and integrality are required only on
full-measure events. Neither simplicity nor infinitely many occurrences is assumed. -/
theorem of_occurrenceTime
    (h : IdentDistrib (fun ω => (N ω).occurrenceTime)
      (fun ω => (N' ω).occurrenceTime) P P')
    (hN : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (N ω) ∧ (N ω).IsIntegerValued)
    (hN' : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (N' ω) ∧ (N' ω).IsIntegerValued) :
    IdentDistrib N N' P P' := by
  classical
  let R (t : ℕ → ℝ≥0∞) : Measure ℝ≥0 :=
    Measure.sum fun n => if t n = ∞ then 0 else Measure.dirac (t n).toNNReal
  have hR : Measurable R := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [R, Measure.sum_apply _ hA]
    have hm (n : ℕ) : Measurable (fun t : ℕ → ℝ≥0∞ =>
        if t n = ∞ then (0 : Measure ℝ≥0) else Measure.dirac (t n).toNNReal) :=
      Measurable.ite (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)
        measurable_const (Measure.measurable_dirac.comp
          (ENNReal.measurable_toNNReal.comp (measurable_pi_apply n)))
    exact Measurable.tsum fun n => (Measure.measurable_coe hA).comp (hm n)
  have hRlaw := h.comp hR
  have heq : R ∘ (fun ω => (N ω).occurrenceTime) =ᵐ[P] N := by
    filter_upwards [hN] with ω hω
    have := hω.1
    exact hω.2.eq_sum_dirac_occurrenceTime.symm
  have heq' : R ∘ (fun ω => (N' ω).occurrenceTime) =ᵐ[P'] N' := by
    filter_upwards [hN'] with ω hω
    have := hω.1
    exact hω.2.eq_sum_dirac_occurrenceTime.symm
  exact (IdentDistrib.of_ae_eq hRlaw.aemeasurable_fst heq).symm.trans
    (hRlaw.trans (IdentDistrib.of_ae_eq hRlaw.aemeasurable_snd heq'))

end ProbabilityTheory.IdentDistrib
