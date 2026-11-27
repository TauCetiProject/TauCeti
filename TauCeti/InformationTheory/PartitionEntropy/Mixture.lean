/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import TauCeti.InformationTheory.PartitionEntropy
import TauCeti.Analysis.SpecialFunctions.Log.MulLog
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Partition entropy of a mixture of probability measures

For probability measures `μ`, `ν` and `a ∈ [0, 1]` (in `ℝ≥0∞`), write `m = a • μ + (1 - a) • ν`
for their mixture. For a countable label `ξ`, concavity of `negMulLog` gives
`a H_μ(ξ) + (1 - a) H_ν(ξ) ≤ H_m(ξ)`. For a measurable `ξ`, subadditivity of `negMulLog`
(`Real.negMulLog_add_le`) with `negMulLog (x * y) = y negMulLog x + x negMulLog y` gives the
reverse inequality up to the bounded error `binEntropy a = negMulLog a + negMulLog (1 - a)`.

## Main results

* `TauCeti.mul_add_mul_le_countablePartitionEntropy_smul_add_smul`:
  `a H_μ(ξ) + (1 - a) H_ν(ξ) ≤ H_m(ξ)`.
* `TauCeti.countablePartitionEntropy_smul_add_smul_le`:
  `H_m(ξ) ≤ a H_μ(ξ) + (1 - a) H_ν(ξ) + binEntropy a`.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Problem 4.6, p. 130.
-/

public section

open MeasureTheory Real
open scoped ENNReal

namespace TauCeti

variable {X ι : Type*} {mX : MeasurableSpace X} {μ ν : Measure X} {a : ℝ≥0∞}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Concavity.** The entropy of a label under a mixture is at least the mixture of its
entropies: `a H_μ(ξ) + (1 - a) H_ν(ξ) ≤ H_{a μ + (1 - a) ν}(ξ)`. -/
theorem mul_add_mul_le_countablePartitionEntropy_smul_add_smul (ha : a ≤ 1) (ξ : X → ι) :
    a * countablePartitionEntropy μ ξ + (1 - a) * countablePartitionEntropy ν ξ ≤
      countablePartitionEntropy (a • μ + (1 - a) • ν) ξ := by
  have ha' : a ≠ ∞ := ha.trans_lt ENNReal.one_lt_top |>.ne
  have hsum : a.toReal + (1 - a).toReal = 1 := by
    rw [← ENNReal.toReal_add ha' (by simp), add_tsub_cancel_of_le ha, ENNReal.toReal_one]
  simp only [countablePartitionEntropy_def, ← ENNReal.tsum_mul_left, ← tsum_add]
  refine tsum_le_tsum fun i ↦ ?_
  have hp0 := measureReal_nonneg (μ := μ) (s := ξ ⁻¹' {i})
  have hq0 := measureReal_nonneg (μ := ν) (s := ξ ⁻¹' {i})
  have hp := negMulLog_nonneg hp0 (measureReal_le_one (μ := μ))
  have hq := negMulLog_nonneg hq0 (measureReal_le_one (μ := ν))
  calc a * ENNReal.ofReal (negMulLog (μ.real (ξ ⁻¹' {i}))) +
        (1 - a) * ENNReal.ofReal (negMulLog (ν.real (ξ ⁻¹' {i})))
      = ENNReal.ofReal (a.toReal * negMulLog (μ.real (ξ ⁻¹' {i})) +
          (1 - a).toReal * negMulLog (ν.real (ξ ⁻¹' {i}))) := by
        simp [ENNReal.ofReal_add, ENNReal.ofReal_mul, mul_nonneg, hp, hq, ha']
    _ ≤ ENNReal.ofReal (negMulLog ((a • μ + (1 - a) • ν).real (ξ ⁻¹' {i}))) := by
        rw [TauCeti.MeasureTheory.measureReal_smul_add_smul_apply ha' (by simp)]
        exact ENNReal.ofReal_le_ofReal (concaveOn_negMulLog.2 hp0 hq0
          ENNReal.toReal_nonneg ENNReal.toReal_nonneg hsum)

variable [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]

/-- **Bounded defect.** The entropy of a measurable label under a mixture exceeds the mixture of
its entropies by at most the binary entropy `binEntropy a = negMulLog a + negMulLog (1 - a)`. -/
theorem countablePartitionEntropy_smul_add_smul_le (ha : a ≤ 1) {ξ : X → ι} (hξ : Measurable ξ) :
    countablePartitionEntropy (a • μ + (1 - a) • ν) ξ ≤
      a * countablePartitionEntropy μ ξ + (1 - a) * countablePartitionEntropy ν ξ +
        ENNReal.ofReal (binEntropy a.toReal) := by
  have ha' : a ≠ ∞ := ha.trans_lt ENNReal.one_lt_top |>.ne
  have hα0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
  have hβ0 : 0 ≤ (1 - a).toReal := ENNReal.toReal_nonneg
  have hα := negMulLog_nonneg hα0 (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa))
  have hβ := negMulLog_nonneg hβ0 (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp))
  have hcell : ∀ i, ENNReal.ofReal (negMulLog ((a • μ + (1 - a) • ν).real (ξ ⁻¹' {i}))) ≤
      a * ENNReal.ofReal (negMulLog (μ.real (ξ ⁻¹' {i}))) +
        (1 - a) * ENNReal.ofReal (negMulLog (ν.real (ξ ⁻¹' {i}))) +
          (ENNReal.ofReal (negMulLog a.toReal) * μ (ξ ⁻¹' {i}) +
            ENNReal.ofReal (negMulLog (1 - a).toReal) * ν (ξ ⁻¹' {i})) := fun i ↦ by
    have hp0 := measureReal_nonneg (μ := μ) (s := ξ ⁻¹' {i})
    have hq0 := measureReal_nonneg (μ := ν) (s := ξ ⁻¹' {i})
    have hp := negMulLog_nonneg hp0 (measureReal_le_one (μ := μ))
    have hq := negMulLog_nonneg hq0 (measureReal_le_one (μ := ν))
    have hreal : negMulLog ((a • μ + (1 - a) • ν).real (ξ ⁻¹' {i})) ≤
        a.toReal * negMulLog (μ.real (ξ ⁻¹' {i})) +
          (1 - a).toReal * negMulLog (ν.real (ξ ⁻¹' {i})) +
          (negMulLog a.toReal * μ.real (ξ ⁻¹' {i}) +
            negMulLog (1 - a).toReal * ν.real (ξ ⁻¹' {i})) := by
      rw [TauCeti.MeasureTheory.measureReal_smul_add_smul_apply ha' (by simp)]
      refine (negMulLog_add_le (mul_nonneg hα0 hp0) (mul_nonneg hβ0 hq0)).trans_eq ?_
      rw [negMulLog_mul, negMulLog_mul]
      ring
    refine (ENNReal.ofReal_le_ofReal hreal).trans_eq ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    simp [ENNReal.ofReal_add, ENNReal.ofReal_mul, mul_nonneg, hp, hq, hα, hβ, ha',
      ofReal_measureReal]
  have hA : ∑' i, μ (ξ ⁻¹' {i}) = 1 := by
    simpa using tsum_measure_inter_preimage_singleton (μ := μ) hξ Set.univ
  have hB : ∑' i, ν (ξ ⁻¹' {i}) = 1 := by
    simpa using tsum_measure_inter_preimage_singleton (μ := ν) hξ Set.univ
  rw [countablePartitionEntropy_def]
  refine (tsum_le_tsum hcell).trans_eq ?_
  rw [tsum_add, tsum_add, tsum_add, ENNReal.tsum_mul_left,
    ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hA, hB, mul_one, mul_one,
    ← ENNReal.ofReal_add hα hβ, ENNReal.toReal_sub_of_le ha ENNReal.one_ne_top,
    ENNReal.toReal_one, ← binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [countablePartitionEntropy_def]

end TauCeti
