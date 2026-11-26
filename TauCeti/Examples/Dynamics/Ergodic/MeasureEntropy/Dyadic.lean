/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.PartitionEntropy
public import TauCeti.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Worked example: dyadic truncations of the identity of `[0, 1]`

On `I = [0, 1]` with Lebesgue measure, the label `x ↦ x` is not admissible: its alphabet `I` is
uncountable. Every one of its atoms is a point, of mass zero, so the countable-partition formula
applied to it would give `0`. Its dyadic truncations `TauCeti.unitInterval.cellIdx (2 ^ k)`, the
index of the dyadic interval `[j / 2 ^ k, (j + 1) / 2 ^ k)` containing `x` (the top one closed at
`1`), are admissible labels into `ℕ`: their `2 ^ k` atoms have mass `2⁻¹ ^ k`, so the truncation
at level `k` has entropy `k log 2`, which tends to `⊤`.
-/

public section

open MeasureTheory Real Filter Topology Set
open scoped ENNReal unitInterval

namespace TauCeti.DyadicEntropyExamples

/-- **Dyadic truncations.** The truncation at level `k` has entropy `k log 2`. -/
theorem countablePartitionEntropy_cellIdx_two_pow (k : ℕ) :
    countablePartitionEntropy volume (unitInterval.cellIdx (2 ^ k)) =
      ENNReal.ofReal (k * log 2) := by
  have hreal (i : Fin (2 ^ k)) :
      (volume : Measure I).real (unitInterval.cellIdx (2 ^ k) ⁻¹' {(i : ℕ)}) = 2⁻¹ ^ k := by
    simp [Measure.real, unitInterval.volume_preimage_cellIdx i.isLt]
  rw [show unitInterval.cellIdx (2 ^ k) = Fin.val ∘ unitInterval.cellFin (2 ^ k) from
      funext fun x ↦ (unitInterval.coe_cellFin x).symm,
    countablePartitionEntropy_comp_of_injective _ Fin.val_injective,
    countablePartitionEntropy_def, tsum_fintype]
  simp only [unitInterval.preimage_cellFin_singleton, hreal, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [negMulLog_def, log_pow, log_inv, inv_pow]
  push_cast
  field_simp

/-- The entropies of the dyadic truncations tend to `⊤`. -/
theorem tendsto_countablePartitionEntropy_cellIdx_two_pow :
    Tendsto (fun k ↦ countablePartitionEntropy volume (unitInterval.cellIdx (2 ^ k))) atTop
      (𝓝 ∞) := by
  simp only [countablePartitionEntropy_cellIdx_two_pow]
  exact ENNReal.tendsto_ofReal_atTop.comp
    (tendsto_natCast_atTop_atTop.atTop_mul_const (log_pos one_lt_two))

/-- The label `x ↦ x` of `[0, 1]` is not admissible: its alphabet `I` is uncountable, since a
countable subset of `ℝ` is Lebesgue-null while `[0, 1]` has measure `1`. -/
example : ¬ Countable I := fun h ↦ by
  simpa using (countable_coe_iff.mp h).measure_zero volume

/-- The countable-partition formula applied to the label `x ↦ x`, whose atoms are points, gives
`0`. Since the label is not admissible, this value is not its entropy. -/
example : countablePartitionEntropy volume (id : I → I) = 0 := by
  rw [countablePartitionEntropy_def]
  exact tsum_eq_zero_iff.mpr fun x ↦ by simp [Measure.real]

end TauCeti.DyadicEntropyExamples
