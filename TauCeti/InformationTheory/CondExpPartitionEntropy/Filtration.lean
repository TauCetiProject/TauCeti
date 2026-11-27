/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.CondExpPartitionEntropy.Countable
public import Mathlib.Probability.Martingale.Convergence
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Conditional entropy along an increasing sequence of σ-algebras

For a filtration `ℱ` and a label `a`, the conditional entropy `H(P | ℱ n)` of the partition given
`ℱ n` converges to `H(P | ⨆ n, ℱ n)`, by Lévy's upward theorem and dominated convergence. This
holds for finite labels under a finite measure, and for countable labels of finite entropy under a
probability measure. Since the conditional entropy decreases along the filtration, the limit is
also the infimum.

## Main results

* `TauCeti.tendsto_condExpPartitionEntropy_iSup` and
  `TauCeti.condExpPartitionEntropy_iSup_eq_iInf`: finite labels.
* `TauCeti.tendsto_condExpCountablePartitionEntropy_iSup` and
  `TauCeti.condExpCountablePartitionEntropy_iSup_eq_iInf`: countable labels of finite entropy.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory* (author notes dated 3 April 2023), Definition 4.2,
  with natural logarithms, for the definition of conditional entropy only. The continuity results
  here follow from Lévy's upward theorem, Mathlib's `MeasureTheory.tendsto_ae_condExp`.
-/

public section

open MeasureTheory Real Set Filter Topology
open scoped ENNReal

namespace TauCeti

variable {X ι : Type*} {mX : MeasurableSpace X} {μ : Measure X}

section Finite

variable [IsFiniteMeasure μ]

/-- One atom of a partition along a filtration: for a finite measure, by Lévy's upward theorem and
dominated convergence, `∫ negMulLog μ[1_{a = i} | ℱ n] → ∫ negMulLog μ[1_{a = i} | ⨆ n, ℱ n]`. -/
theorem tendsto_integral_negMulLog_condAtomProb_iSup (ℱ : Filtration ℕ mX) (a : X → ι)
    (i : ι) :
    Tendsto (fun n ↦ ∫ x, negMulLog (condAtomProb μ (ℱ n) a i x) ∂μ) atTop
      (𝓝 (∫ x, negMulLog (condAtomProb μ (⨆ n, ℱ n) a i x) ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ)) (fun n ↦ ?_)
    (integrable_const 1) (fun n ↦ ?_) ?_
  · exact continuous_negMulLog.comp_aestronglyMeasurable
      ((stronglyMeasurable_condAtomProb (μ := μ) (m := ℱ n) a i).mono
        (ℱ.le n)).aestronglyMeasurable
  · filter_upwards [condAtomProb_mem_Icc (μ := μ) (m := ℱ n) a i] with x hx
    rw [Real.norm_of_nonneg (negMulLog_nonneg hx.1 hx.2)]
    exact (negMulLog_le_one_sub_self hx.1).trans (by linarith [hx.1])
  · filter_upwards [tendsto_ae_condExp (μ := μ) (ℱ := ℱ) ((a ⁻¹' {i}).indicator (1 : X → ℝ))]
      with x hx
    simp only [condAtomProb_def]
    exact (continuous_negMulLog.tendsto _).comp hx

/-- **Continuity along increasing σ-algebras, finite labels.** For a filtration `ℱ`,
`H(P | ℱ n) → H(P | ⨆ n, ℱ n)`. -/
theorem tendsto_condExpPartitionEntropy_iSup [Fintype ι] (ℱ : Filtration ℕ mX) (a : X → ι) :
    Tendsto (fun n ↦ condExpPartitionEntropy μ (ℱ n) a) atTop
      (𝓝 (condExpPartitionEntropy μ (⨆ n, ℱ n) a)) := by
  simp_rw [condExpPartitionEntropy_eq_sum]
  exact tendsto_finsetSum _ fun i _ ↦ tendsto_integral_negMulLog_condAtomProb_iSup ℱ a i

/-- Along a filtration the conditional entropy of a finite partition decreases to its value given
`⨆ n, ℱ n`: `H(P | ⨆ n, ℱ n) = ⨅ n, H(P | ℱ n)`. -/
theorem condExpPartitionEntropy_iSup_eq_iInf [Fintype ι] (ℱ : Filtration ℕ mX) (a : X → ι) :
    condExpPartitionEntropy μ (⨆ n, ℱ n) a = ⨅ n, condExpPartitionEntropy μ (ℱ n) a :=
  tendsto_nhds_unique (tendsto_condExpPartitionEntropy_iSup ℱ a)
    (tendsto_atTop_ciInf (fun _ _ hnk ↦ condExpPartitionEntropy_anti (ℱ.mono hnk) a)
      ⟨0, forall_mem_range.2 fun _ ↦ condExpPartitionEntropy_nonneg _ a⟩)

end Finite

section Probability

variable [IsProbabilityMeasure μ]

/-- **Continuity along increasing σ-algebras, countable labels.** For a probability measure, a
filtration `ℱ` and a countable label of finite entropy, `H(P | ℱ n) → H(P | ⨆ n, ℱ n)`. The
entropies `negMulLog (μ.real (a ⁻¹' {i}))` of the atoms dominate the terms. -/
theorem tendsto_condExpCountablePartitionEntropy_iSup [Countable ι] (ℱ : Filtration ℕ mX)
    {a : X → ι} (ha : countablePartitionEntropy μ a ≠ ∞) :
    Tendsto (fun n ↦ condExpCountablePartitionEntropy μ (ℱ n) a) atTop
      (𝓝 (condExpCountablePartitionEntropy μ (⨆ n, ℱ n) a)) := by
  set f : ℕ → ι → ℝ := fun n i ↦ ∫ x, negMulLog (condAtomProb μ (ℱ n) a i x) ∂μ with hf
  set g : ι → ℝ := fun i ↦ ∫ x, negMulLog (condAtomProb μ (⨆ n, ℱ n) a i x) ∂μ with hg
  set B : ι → ℝ := fun i ↦ negMulLog (μ.real (a ⁻¹' {i})) with hB
  have hB_nn : ∀ i, 0 ≤ B i := fun i ↦ negMulLog_nonneg measureReal_nonneg measureReal_le_one
  have hB_sum : Summable B := by
    rw [countablePartitionEntropy_def] at ha
    exact (ENNReal.summable_toReal ha).congr fun i ↦ ENNReal.toReal_ofReal (hB_nn i)
  have hf_nn : ∀ n i, 0 ≤ f n i := fun n i ↦ integral_negMulLog_condAtomProb_nonneg _ a i
  have hg_nn : ∀ i, 0 ≤ g i := fun i ↦ integral_negMulLog_condAtomProb_nonneg _ a i
  have hf_le : ∀ n i, f n i ≤ B i := fun n i ↦ integral_negMulLog_condAtomProb_le a i
  have hg_le : ∀ i, g i ≤ B i := fun i ↦ integral_negMulLog_condAtomProb_le a i
  have hsum : Tendsto (fun n ↦ ∑' i, f n i) atTop (𝓝 (∑' i, g i)) :=
    tendsto_tsum_of_dominated_convergence hB_sum
      (fun i ↦ tendsto_integral_negMulLog_condAtomProb_iSup ℱ a i)
      (.of_forall fun n i ↦ by rw [Real.norm_of_nonneg (hf_nn n i)]; exact hf_le n i)
  have hfeq : ∀ n, condExpCountablePartitionEntropy μ (ℱ n) a = ENNReal.ofReal (∑' i, f n i) :=
    fun n ↦ by
      rw [condExpCountablePartitionEntropy_eq_tsum, ENNReal.ofReal_tsum_of_nonneg (hf_nn n)
        (hB_sum.of_nonneg_of_le (hf_nn n) (hf_le n))]
  have hgeq : condExpCountablePartitionEntropy μ (⨆ n, ℱ n) a = ENNReal.ofReal (∑' i, g i) := by
    rw [condExpCountablePartitionEntropy_eq_tsum, ENNReal.ofReal_tsum_of_nonneg hg_nn
      (hB_sum.of_nonneg_of_le hg_nn hg_le)]
  simp_rw [hfeq, hgeq]
  exact ENNReal.tendsto_ofReal hsum

/-- Along a filtration the conditional entropy of a countable partition of finite entropy decreases
to its value given `⨆ n, ℱ n`: `H(P | ⨆ n, ℱ n) = ⨅ n, H(P | ℱ n)`. -/
theorem condExpCountablePartitionEntropy_iSup_eq_iInf [Countable ι] (ℱ : Filtration ℕ mX)
    {a : X → ι} (ha : countablePartitionEntropy μ a ≠ ∞) :
    condExpCountablePartitionEntropy μ (⨆ n, ℱ n) a =
      ⨅ n, condExpCountablePartitionEntropy μ (ℱ n) a :=
  tendsto_nhds_unique (tendsto_condExpCountablePartitionEntropy_iSup ℱ ha)
    (tendsto_atTop_iInf fun _ _ hnk ↦ condExpCountablePartitionEntropy_anti (ℱ.mono hnk) a)

end Probability

end TauCeti
