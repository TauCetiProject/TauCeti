/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.CondExpPartitionEntropy.CountableLabel
public import Mathlib.Probability.Martingale.Convergence
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Conditional entropy of a countable label given a sub-σ-algebra

Let `μ` be a measure on `X`, `m` a σ-algebra on `X` and `a : X → ι` a label into a countable type,
representing a countable partition. With the conditional probabilities
`pᵢ = TauCeti.condAtomProb μ m a i = μ[1_{a = i} | m]`, the conditional entropy of the partition
given `m` is

`condExpCountablePartitionEntropy μ m a = ∫⁻ x, ∑' i, ENNReal.ofReal (negMulLog (pᵢ x)) ∂μ`,

in `[0, ∞]` and in natural units. This extends `TauCeti.condExpPartitionEntropy` from finite to
countable labels. No standard-Borel or countable-generation hypothesis is placed on `X`.

The second part proves the continuity of conditional entropy along an increasing sequence of
σ-algebras, by Lévy's upward theorem: for a filtration `ℱ`, `H(P | ℱ n) → H(P | ⨆ n, ℱ n)` for
finite labels, and for countable labels of finite entropy under a probability measure.

## Main results

* `TauCeti.condExpCountablePartitionEntropy_congr`: the value does not depend on the
  representatives of the conditional probabilities.
* `TauCeti.condExpCountablePartitionEntropy_eq_tsum`: for a finite measure, the sum over the
  atoms of the integrals of `negMulLog pᵢ`.
* `TauCeti.condExpCountablePartitionEntropy_eq_ofReal`: agreement with
  `TauCeti.condExpPartitionEntropy` on finite labels.
* `TauCeti.condExpCountablePartitionEntropy_comap_eq_conditionalPartitionEntropy`: given the
  σ-algebra of a countable label `b`, agreement with `TauCeti.conditionalPartitionEntropy μ a b`.
* `TauCeti.condExpCountablePartitionEntropy_le`, `TauCeti.condExpCountablePartitionEntropy_anti`,
  `TauCeti.condExpCountablePartitionEntropy_bot` and
  `TauCeti.condExpCountablePartitionEntropy_eq_zero_of_measurableSet`:
  `H(P | m) ≤ H(P)`, antitonicity in `m`, `H(P | ⊥) = H(P)`, and `H(P | m) = 0` when the atoms are
  measurable for `m`.
* `TauCeti.tendsto_condExpPartitionEntropy_iSup` and
  `TauCeti.tendsto_condExpCountablePartitionEntropy_iSup`: continuity along increasing sequences
  of σ-algebras.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory* (author notes dated 3 April 2023), Definition 4.2,
  with natural logarithms.
-/

public section

open MeasureTheory Real Set Filter Topology
open scoped ENNReal

namespace TauCeti

variable {X ι κ : Type*} {m m₁ m₂ : MeasurableSpace X} {mX : MeasurableSpace X} {μ : Measure X}

/-- The conditional entropy of the countable partition given by the label `a`, given the
σ-algebra `m`: `∫⁻ x, ∑' i, ENNReal.ofReal (negMulLog (pᵢ x)) ∂μ` with `pᵢ = μ[1_{a = i} | m]`. -/
noncomputable def condExpCountablePartitionEntropy (μ : Measure X) (m : MeasurableSpace X)
    (a : X → ι) : ℝ≥0∞ :=
  ∫⁻ x, ∑' i, ENNReal.ofReal (negMulLog (condAtomProb μ m a i x)) ∂μ

/-- Unfolding lemma for `TauCeti.condExpCountablePartitionEntropy`. -/
theorem condExpCountablePartitionEntropy_def (μ : Measure X) (m : MeasurableSpace X)
    (a : X → ι) :
    condExpCountablePartitionEntropy μ m a =
      ∫⁻ x, ∑' i, ENNReal.ofReal (negMulLog (condAtomProb μ m a i x)) ∂μ :=
  (rfl)

/-- The conditional entropy does not depend on the representatives of the conditional
probabilities. -/
theorem condExpCountablePartitionEntropy_congr [Countable ι] {a : X → ι} {p : ι → X → ℝ}
    (hp : ∀ i, p i =ᵐ[μ] condAtomProb μ m a i) :
    condExpCountablePartitionEntropy μ m a =
      ∫⁻ x, ∑' i, ENNReal.ofReal (negMulLog (p i x)) ∂μ := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_all_iff.2 hp] with x hx
  exact tsum_congr fun i ↦ by rw [hx i]

/-- If the atoms are measurable for `m`, the conditional entropy given `m` is zero. In particular
conditioning on the ambient σ-algebra, or on the label itself, gives zero. -/
theorem condExpCountablePartitionEntropy_eq_zero_of_measurableSet {a : X → ι}
    (ha : ∀ i, MeasurableSet[m] (a ⁻¹' {i})) :
    condExpCountablePartitionEntropy μ m a = 0 := by
  have h0 : ∀ i x, negMulLog (condAtomProb μ m a i x) = 0 := fun i x ↦ by
    rcases condAtomProb_eq_indicator_or_zero_of_measurableSet (μ := μ) (ha i) with h | h
    · by_cases hx : x ∈ a ⁻¹' {i} <;> simp [h, hx]
    · simp [h]
  simp [condExpCountablePartitionEntropy_def, h0]

section Finite

variable [IsFiniteMeasure μ]

/-- For a finite measure, the conditional entropy of a countable label is the sum over the atoms
of the integrals of `negMulLog pᵢ`. -/
theorem condExpCountablePartitionEntropy_eq_tsum [Countable ι] (m : MeasurableSpace X)
    (a : X → ι) :
    condExpCountablePartitionEntropy μ m a =
      ∑' i, ENNReal.ofReal (∫ x, negMulLog (condAtomProb μ m a i x) ∂μ) := by
  rw [condExpCountablePartitionEntropy_def, lintegral_tsum fun i ↦
    (integrable_negMulLog_condAtomProb a i).aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  refine tsum_congr fun i ↦ (ofReal_integral_eq_lintegral_ofReal
    (integrable_negMulLog_condAtomProb a i) ?_).symm
  filter_upwards [condAtomProb_mem_Icc (μ := μ) (m := m) a i] with x hx
  exact negMulLog_nonneg hx.1 hx.2

/-- **Finite labels.** On a finite label the conditional entropy is `ENNReal.ofReal` of
`TauCeti.condExpPartitionEntropy`. -/
theorem condExpCountablePartitionEntropy_eq_ofReal [Fintype ι] (m : MeasurableSpace X)
    (a : X → ι) :
    condExpCountablePartitionEntropy μ m a = ENNReal.ofReal (condExpPartitionEntropy μ m a) := by
  rw [condExpCountablePartitionEntropy_eq_tsum, tsum_fintype, condExpPartitionEntropy_eq_sum]
  exact (ENNReal.ofReal_sum_of_nonneg fun i _ ↦
    integral_negMulLog_condAtomProb_nonneg (μ := μ) m a i).symm

/-- **Monotonicity.** Enlarging the σ-algebra decreases the conditional entropy:
`H(P | m₂) ≤ H(P | m₁)` for `m₁ ≤ m₂`. -/
theorem condExpCountablePartitionEntropy_anti [Countable ι] (h₁₂ : m₁ ≤ m₂) (a : X → ι) :
    condExpCountablePartitionEntropy μ m₂ a ≤ condExpCountablePartitionEntropy μ m₁ a := by
  rw [condExpCountablePartitionEntropy_eq_tsum, condExpCountablePartitionEntropy_eq_tsum]
  exact tsum_le_tsum fun i ↦
    ENNReal.ofReal_le_ofReal (integral_negMulLog_condAtomProb_anti h₁₂ a i)

/-- **Conditioning on a countable label.** For a finite measure, a countable partition with
null-measurable atoms and a measurable countable label `b`, the conditional entropy given the
σ-algebra generated by `b` is `TauCeti.conditionalPartitionEntropy μ a b`. -/
theorem condExpCountablePartitionEntropy_comap_eq_conditionalPartitionEntropy [Countable ι]
    [Countable κ] [mκ : MeasurableSpace κ] [MeasurableSingletonClass κ] {b : X → κ}
    (hb : Measurable b) {a : X → ι} (ha : ∀ i, NullMeasurableSet (a ⁻¹' {i}) μ) :
    condExpCountablePartitionEntropy μ (mκ.comap b) a = conditionalPartitionEntropy μ a b := by
  rw [condExpCountablePartitionEntropy_eq_tsum, conditionalPartitionEntropy_def,
    tsum_prod']
  exact tsum_congr fun i ↦ ofReal_integral_negMulLog_condAtomProb_comap hb (ha i)

/-- One atom of a finite partition along a filtration: by Lévy's upward theorem and dominated
convergence, `∫ negMulLog μ[1_{a = i} | ℱ n] → ∫ negMulLog μ[1_{a = i} | ⨆ n, ℱ n]`. -/
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

/-- **Upper bound.** For a probability measure, `H(P | m) ≤ H(P)`, where `H(P)` is
`TauCeti.countablePartitionEntropy μ a`. -/
theorem condExpCountablePartitionEntropy_le [Countable ι] (m : MeasurableSpace X) (a : X → ι) :
    condExpCountablePartitionEntropy μ m a ≤ countablePartitionEntropy μ a := by
  rw [condExpCountablePartitionEntropy_eq_tsum, countablePartitionEntropy_def]
  exact tsum_le_tsum fun i ↦
    ENNReal.ofReal_le_ofReal (integral_negMulLog_condAtomProb_le a i)

/-- **Trivial σ-algebra.** For a probability measure and null-measurable atoms,
`H(P | ⊥) = H(P)`. -/
theorem condExpCountablePartitionEntropy_bot [Countable ι] {a : X → ι}
    (ha : ∀ i, NullMeasurableSet (a ⁻¹' {i}) μ) :
    condExpCountablePartitionEntropy μ ⊥ a = countablePartitionEntropy μ a := by
  rw [condExpCountablePartitionEntropy_eq_tsum, countablePartitionEntropy_def]
  refine tsum_congr fun i ↦ ?_
  rw [condAtomProb_bot (ha i)]
  simp

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

end Probability

end TauCeti
