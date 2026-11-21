/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Marking.Measure
public import TauCeti.Probability.PointProcess.OccurrenceTime.Reconstruction

/-!
# Independent marking of ordered occurrence times on `ℝ≥0`

On the nonnegative half-line `ℝ≥0`, canonical independent marking `Kernel.marking` of any locally
finite integer-valued measure agrees with independently marking its ordered finite
`Measure.occurrenceTime`s via `Kernel.optionalTupleMarking`.

Keeping this temporal identification in its own module avoids pulling the `ℝ≥0` occurrence-time
theory into the general marking kernel module `TauCeti.Probability.PointProcess.Marking.Measure`.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapter 5 (independent marking).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

/-- On the half-line `ℝ≥0`, canonical independent marking of any locally finite integer-valued
measure agrees with independently marking its ordered finite `Measure.occurrenceTime`s. -/
theorem marking_eq_optionalTupleMarking_occurrenceTime {E : Type*} [MeasurableSpace E]
    (κ : Kernel ℝ≥0 E) [IsMarkovKernel κ] {μ : Measure ℝ≥0} [IsLocallyFiniteMeasure μ]
    (hμ : μ.IsIntegerValued) :
    κ.marking μ = κ.optionalTupleMarking ℕ (fun n =>
      if μ.occurrenceTime n = ∞ then none else some (μ.occurrenceTime n).toNNReal) := by
  apply κ.marking_eq_optionalTupleMarking
    (fun n => (isCompact_compactCovering ℝ≥0 n).measure_ne_top)
  conv_lhs => rw [hμ.eq_occurrenceTimeMeasure, TauCeti.Probability.occurrenceTimeMeasure_def]
  congr 1
  funext n
  split_ifs <;> rfl

end ProbabilityTheory.Kernel
