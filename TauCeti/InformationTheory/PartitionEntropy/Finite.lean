/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.LabelEntropy
public import TauCeti.InformationTheory.PartitionEntropy
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Partition entropy of labels with finitely many values

On a label with finitely many values, the extended partition entropies
`TauCeti.countablePartitionEntropy` and `TauCeti.conditionalPartitionEntropy` are the real
finite-label entropies `TauCeti.labelEntropy` and `TauCeti.condLabelEntropy`, mapped into `ℝ≥0∞`.

## Main results

* `TauCeti.countablePartitionEntropy_eq_ofReal_labelEntropy`: under a probability (or zero)
  measure, `countablePartitionEntropy μ a = ENNReal.ofReal (labelEntropy μ a)`.
* `TauCeti.conditionalPartitionEntropy_eq_ofReal_condLabelEntropy`: for every measure,
  `conditionalPartitionEntropy μ a b = ENNReal.ofReal (condLabelEntropy μ a b)`.
* `TauCeti.countablePartitionEntropy_ne_top` and `TauCeti.conditionalPartitionEntropy_ne_top`:
  for every measure, both are finite on finite alphabets.
* `TauCeti.toReal_countablePartitionEntropy` (under a probability or zero measure) and
  `TauCeti.toReal_conditionalPartitionEntropy` (for every measure): their real parts are the
  finite-label entropies.
-/

public section

open MeasureTheory Real
open scoped ENNReal

namespace TauCeti

variable {X ι κ : Type*} {mX : MeasurableSpace X} {μ : Measure X} [Fintype ι] [Fintype κ]

/-- On a finite alphabet, under a probability (or zero) measure, the partition entropy of a label
is its finite-label entropy. -/
theorem countablePartitionEntropy_eq_ofReal_labelEntropy [IsZeroOrProbabilityMeasure μ]
    (a : X → ι) : countablePartitionEntropy μ a = ENNReal.ofReal (labelEntropy μ a) := by
  rw [labelEntropy_def, countablePartitionEntropy_def, tsum_fintype, ENNReal.ofReal_sum_of_nonneg]
  exact fun _ _ ↦ negMulLog_nonneg measureReal_nonneg measureReal_le_one

/-- On a finite alphabet, for every measure, the partition entropy of a label is finite. -/
theorem countablePartitionEntropy_ne_top {ι : Type*} [Finite ι] (μ : Measure X) (a : X → ι) :
    countablePartitionEntropy μ a ≠ ∞ := by
  have := Fintype.ofFinite ι
  rw [countablePartitionEntropy_def, tsum_fintype]
  exact ENNReal.sum_ne_top.mpr fun _ _ ↦ ENNReal.ofReal_ne_top

/-- On a finite alphabet, under a probability (or zero) measure, the real part of the partition
entropy of a label is its finite-label entropy. -/
theorem toReal_countablePartitionEntropy [IsZeroOrProbabilityMeasure μ] (a : X → ι) :
    (countablePartitionEntropy μ a).toReal = labelEntropy μ a := by
  rw [countablePartitionEntropy_eq_ofReal_labelEntropy,
    ENNReal.toReal_ofReal (labelEntropy_nonneg a)]

/-- On finite alphabets, for every measure, the conditional partition entropy of `a` given `b` is
the finite-label conditional entropy. -/
theorem conditionalPartitionEntropy_eq_ofReal_condLabelEntropy (μ : Measure X) (a : X → ι)
    (b : X → κ) :
    conditionalPartitionEntropy μ a b = ENNReal.ofReal (condLabelEntropy μ a b) := by
  have h i j := measureReal_inter_mul_log_div_nonneg μ (a ⁻¹' {i}) (b ⁻¹' {j})
  rw [conditionalPartitionEntropy_def, tsum_fintype, Fintype.sum_prod_type, condLabelEntropy_def,
    ENNReal.ofReal_sum_of_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ h i j]
  exact Finset.sum_congr rfl fun i _ ↦ (ENNReal.ofReal_sum_of_nonneg fun j _ ↦ h i j).symm

/-- On finite alphabets, for every measure, the conditional partition entropy is finite. -/
theorem conditionalPartitionEntropy_ne_top {ι κ : Type*} [Finite ι] [Finite κ] (μ : Measure X)
    (a : X → ι) (b : X → κ) : conditionalPartitionEntropy μ a b ≠ ∞ := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  rw [conditionalPartitionEntropy_eq_ofReal_condLabelEntropy]
  exact ENNReal.ofReal_ne_top

/-- On finite alphabets, for every measure, the real part of the conditional partition entropy is
the finite-label conditional entropy. -/
theorem toReal_conditionalPartitionEntropy (μ : Measure X) (a : X → ι) (b : X → κ) :
    (conditionalPartitionEntropy μ a b).toReal = condLabelEntropy μ a b := by
  rw [conditionalPartitionEntropy_eq_ofReal_condLabelEntropy,
    ENNReal.toReal_ofReal (condLabelEntropy_nonneg μ a b)]

end TauCeti
