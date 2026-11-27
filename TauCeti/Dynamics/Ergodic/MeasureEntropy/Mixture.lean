/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.MeasureEntropy.Basic
public import TauCeti.InformationTheory.PartitionEntropy.Mixture
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Convex

/-!
# Entropy of mixtures of invariant probabilities

For probability measures `μ`, `ν` and `a ∈ [0, 1]` (in `ℝ≥0∞`), write `m = a • μ + (1 - a) • ν`
for their mixture. For a measurable countable label `ξ`, the entropy `H_m(ξ)` lies between
`a H_μ(ξ) + (1 - a) H_ν(ξ)` and that value plus the bounded error
`binEntropy a = negMulLog a + negMulLog (1 - a)`
(`TauCeti.mul_add_mul_le_countablePartitionEntropy_smul_add_smul` and
`TauCeti.countablePartitionEntropy_smul_add_smul_le`). Applied to itineraries and divided by `n`,
the error disappears, so entropy rates are affine in the measure:
`h_m(T, ξ) = a h_μ(T, ξ) + (1 - a) h_ν(T, ξ)` when `T` preserves `μ` and `ν`. Taking suprema
gives `h_m(T) ≤ a h_μ(T) + (1 - a) h_ν(T)`.

The reverse inequality for the Kolmogorov–Sinai entropy needs a single label that is good for
`μ` and for `ν` at once, and is not proved here.

## Main results

* `TauCeti.partitionEntropyRate_smul_add_smul`:
  `h_m(T, ξ) = a h_μ(T, ξ) + (1 - a) h_ν(T, ξ)`.
* `TauCeti.measureEntropy_smul_add_smul_le`: `h_m(T) ≤ a h_μ(T) + (1 - a) h_ν(T)`.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory*, 2023, Problem 4.6, p. 130.
-/

public section

open MeasureTheory Real Filter Topology
open scoped ENNReal

namespace TauCeti

variable {X ι : Type*} {mX : MeasurableSpace X} {μ ν : Measure X} {a : ℝ≥0∞}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι] {T : X → X}

/-- **Affinity of entropy rates.** For a map preserving the probability measures `μ` and `ν` and
a measurable countable label `ξ`, the entropy rate under the mixture `a • μ + (1 - a) • ν` is
`a h_μ(T, ξ) + (1 - a) h_ν(T, ξ)`. -/
theorem partitionEntropyRate_smul_add_smul (ha : a ≤ 1) (hμ : MeasurePreserving T μ μ)
    (hν : MeasurePreserving T ν ν) {ξ : X → ι} (hξ : Measurable ξ) :
    partitionEntropyRate (a • μ + (1 - a) • ν) T ξ =
      a * partitionEntropyRate μ T ξ + (1 - a) * partitionEntropyRate ν T ξ := by
  have ha' : a ≠ ∞ := ha.trans_lt ENNReal.one_lt_top |>.ne
  have := MeasureTheory.isProbabilityMeasure_smul_add_smul (add_tsub_cancel_of_le ha) μ ν
  set c := ENNReal.ofReal (binEntropy a.toReal)
  have hb := measurable_iteratedPartitionLabel hμ.measurable hξ
  set g : ℕ → ℝ≥0∞ := fun n ↦
    a * (countablePartitionEntropy μ (iteratedPartitionLabel T ξ n) / n) +
      (1 - a) * (countablePartitionEntropy ν (iteratedPartitionLabel T ξ n) / n)
  have hg : Tendsto g atTop
      (𝓝 (a * partitionEntropyRate μ T ξ + (1 - a) * partitionEntropyRate ν T ξ)) :=
    (ENNReal.Tendsto.const_mul (tendsto_partitionEntropyRate hμ hξ) (Or.inr ha')).add
      (ENNReal.Tendsto.const_mul (tendsto_partitionEntropyRate hν hξ) (Or.inr (by simp)))
  have hc : Tendsto (fun n : ℕ ↦ c * (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul ENNReal.tendsto_inv_nat_nhds_zero
      (Or.inr ENNReal.ofReal_ne_top)
  have hgc := hg.add hc
  rw [add_zero] at hgc
  have hsplit : ∀ n : ℕ, (a * countablePartitionEntropy μ (iteratedPartitionLabel T ξ n) +
      (1 - a) * countablePartitionEntropy ν (iteratedPartitionLabel T ξ n)) / n = g n :=
    fun n ↦ by simp only [g, ENNReal.add_div, mul_div_assoc]
  refine tendsto_nhds_unique
    (tendsto_partitionEntropyRate ((hμ.smul_measure a).add_measure (hν.smul_measure (1 - a))) hξ)
    (tendsto_of_tendsto_of_tendsto_of_le_of_le hg hgc (fun n ↦ ?_) (fun n ↦ ?_))
  · rw [← hsplit]
    exact ENNReal.div_le_div_right
      (mul_add_mul_le_countablePartitionEntropy_smul_add_smul ha _) _
  · refine (ENNReal.div_le_div_right
      (countablePartitionEntropy_smul_add_smul_le ha (hb n)) _).trans_eq ?_
    rw [ENNReal.add_div, hsplit, div_eq_mul_inv]

/-- **Upper bound for mixtures.** For a map preserving the probability measures `μ` and `ν`,
`h_{a μ + (1 - a) ν}(T) ≤ a h_μ(T) + (1 - a) h_ν(T)`. -/
theorem measureEntropy_smul_add_smul_le (ha : a ≤ 1) (hμ : MeasurePreserving T μ μ)
    (hν : MeasurePreserving T ν ν) :
    measureEntropy (a • μ + (1 - a) • ν) T ≤
      a * measureEntropy μ T + (1 - a) * measureEntropy ν T := by
  refine measureEntropy_le_iff.2 fun ξ hξ hfin ↦ ?_
  rw [partitionEntropyRate_smul_add_smul ha hμ hν hξ]
  have hlow := mul_add_mul_le_countablePartitionEntropy_smul_add_smul (μ := μ) (ν := ν) ha ξ
  refine add_le_add ?_ ?_
  · rcases eq_or_ne a 0 with rfl | ha0
    · simp
    gcongr
    exact partitionEntropyRate_le_measureEntropy hξ (ENNReal.lt_top_of_mul_ne_top_right
      (ne_top_of_le_ne_top hfin (le_add_right le_rfl |>.trans hlow)) ha0).ne
  · rcases eq_or_ne (1 - a) 0 with h0 | hb0
    · simp [h0]
    gcongr
    exact partitionEntropyRate_le_measureEntropy hξ (ENNReal.lt_top_of_mul_ne_top_right
      (ne_top_of_le_ne_top hfin (le_add_left le_rfl |>.trans hlow)) hb0).ne

end TauCeti
