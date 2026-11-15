/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.OccurrenceTime.Reconstruction
public import Mathlib.Probability.Process.Stopping

/-!
# Occurrence times and the information in cumulative counts

An adapted cumulative-mass process has stopping times given by its ordered
`Measure.occurrenceTime`s. Local finiteness ensures that the threshold is attained,
so this holds for the original filtration, without a right-continuity or completeness
assumption. For integer-valued measures the converse holds as well: the count process
is adapted exactly when all the occurrence times are stopping times.

The finite prefix through occurrence `n` is measurable for the sigma-algebra at
that occurrence. This supplies the past arrival coordinates used when restarting a
counting process to identify successive interarrival laws. Missing occurrences retain
the value infinity; atoms at zero and multiple occurrences are allowed.

## References

* Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, Cambridge
  University Press, 2018, Chapter 7, especially Theorem 7.2.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory.Adapted

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {N : Ω → Measure ℝ≥0}

/-- Occurrence times of adapted cumulative masses are stopping times in the given
filtration. Local finiteness is pathwise; neither integrality nor simplicity is needed. -/
theorem isStoppingTime_occurrenceTime
    (hN : Adapted ℱ (fun t ω => N ω (Iic t)))
    (hloc : ∀ ω, IsLocallyFiniteMeasure (N ω)) (n : ℕ) :
    IsStoppingTime ℱ (fun ω => (N ω).occurrenceTime n) := by
  intro t
  -- Stopping times use WithTop ℝ≥0; ENNReal has the same carrier and inherited order.
  change MeasurableSet[ℱ t] {ω | (N ω).occurrenceTime n ≤ (t : ℝ≥0∞)}
  have heq : {ω | (N ω).occurrenceTime n ≤ t} =
      {ω | (n + 1 : ℝ≥0∞) ≤ N ω (Iic t)} := by
    ext ω
    let := hloc ω
    exact (N ω).occurrenceTime_le_iff n t
  rw [heq]
  exact measurableSet_le measurable_const (hN t)

/-- At occurrence `n`, the entire prefix of occurrence times through index `n`
is measurable for the stopped sigma-algebra. This includes infinite occurrence times
and retains multiplicities rather than requiring strictly increasing times. -/
theorem measurable_occurrenceTime_prefix
    (hN : Adapted ℱ (fun t ω => N ω (Iic t)))
    (hloc : ∀ ω, IsLocallyFiniteMeasure (N ω)) (n : ℕ) :
    Measurable[(hN.isStoppingTime_occurrenceTime hloc n).measurableSpace]
      (fun ω (i : Fin (n + 1)) => (N ω).occurrenceTime i) := by
  have hτ := hN.isStoppingTime_occurrenceTime hloc
  let : MeasurableSpace Ω := (hτ n).measurableSpace
  refine measurable_pi_iff.mpr fun i => ?_
  exact (hτ i).measurable.mono
    ((hτ i).measurableSpace_mono (hτ n)
      (fun ω => (N ω).monotone_occurrenceTime (Nat.le_of_lt_succ i.isLt))) le_rfl

end MeasureTheory.Adapted

namespace TauCeti.Probability

variable {Ω : Type*} {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
  {N : Ω → Measure ℝ≥0}

/-- For locally finite counting measures, adaptation of the cumulative counts is
equivalent to the stopping-time property of every ordered occurrence. No probability
measure, topology on the sample space, or augmentation of the filtration is required. -/
theorem adapted_apply_Iic_iff_isStoppingTime_occurrenceTime
    (hloc : ∀ ω, IsLocallyFiniteMeasure (N ω))
    (hint : ∀ ω, (N ω).IsIntegerValued) :
    Adapted ℱ (fun t ω => N ω (Iic t)) ↔
      ∀ n, IsStoppingTime ℱ (fun ω => (N ω).occurrenceTime n) := by
  refine ⟨fun hN n => hN.isStoppingTime_occurrenceTime hloc n, fun hτ t => ?_⟩
  classical
  let : MeasurableSpace Ω := ℱ t
  dsimp only
  have heq : (fun ω => N ω (Iic t)) =
      (fun ω => ∑' n : ℕ, if (N ω).occurrenceTime n ≤ t then (1 : ℝ≥0∞) else 0) := by
    funext ω
    let := hloc ω
    exact (hint ω).apply_Iic_eq_tsum_occurrenceTime t
  exact heq.symm ▸ Measurable.tsum (fun n =>
    Measurable.ite ((hτ n).measurableSet_le t) measurable_const measurable_const)

end TauCeti.Probability
