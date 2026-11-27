/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.CondExpPartitionEntropy.CountableLabel

/-!
# Conditional entropy of a countable label given a sub-σ-algebra

Let `μ` be a measure on `X`, `m` a σ-algebra on `X` and `a : X → ι` a label into a countable type,
representing a countable partition. With the conditional probabilities
`pᵢ = TauCeti.condAtomProb μ m a i = μ[1_{a = i} | m]`, the conditional entropy of the partition
given `m` is

`condExpCountablePartitionEntropy μ m a = ∫⁻ x, ∑' i, ENNReal.ofReal (negMulLog (pᵢ x)) ∂μ`,

in `[0, ∞]` and in natural units. This extends `TauCeti.condExpPartitionEntropy` from finite to
countable labels. No standard-Borel or countable-generation hypothesis is placed on `X`.

The continuity along increasing sequences of σ-algebras is in
`TauCeti.InformationTheory.CondExpPartitionEntropy.Filtration`.

## Main results

* `TauCeti.condExpCountablePartitionEntropy_congr`: the value does not depend on the
  representatives of the conditional probabilities.
* `TauCeti.condExpCountablePartitionEntropy_eq_tsum`: for a finite measure, the sum over the
  atoms of the integrals of `negMulLog pᵢ`.
* `TauCeti.condExpCountablePartitionEntropy_eq_ofReal`: agreement with
  `TauCeti.condExpPartitionEntropy` on finite labels.
* `TauCeti.condExpCountablePartitionEntropy_comap_eq_conditionalPartitionEntropy`: given the
  σ-algebra of a countable label `b`, agreement with `TauCeti.conditionalPartitionEntropy μ a b`;
  `TauCeti.ofReal_condExpPartitionEntropy_comap_eq_conditionalPartitionEntropy` and
  `TauCeti.condExpPartitionEntropy_comap_eq_toReal_conditionalPartitionEntropy` are its
  finite-label forms for `TauCeti.condExpPartitionEntropy`.
* `TauCeti.condExpCountablePartitionEntropy_le`, `TauCeti.condExpCountablePartitionEntropy_anti`,
  `TauCeti.condExpCountablePartitionEntropy_bot` and
  `TauCeti.condExpCountablePartitionEntropy_eq_zero_of_measurableSet`:
  `H(P | m) ≤ H(P)`, antitonicity in `m`, `H(P | ⊥) = H(P)`, and `H(P | m) = 0` when the atoms are
  measurable for `m`.

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
  simp [condExpCountablePartitionEntropy_def,
    negMulLog_condAtomProb_eq_zero_of_measurableSet (ha _)]

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

/-- **Agreement with the conditional partition entropy, finite labels.** For a finite measure, a
finite partition with null-measurable atoms and a measurable countable label `b`, the conditional
entropy given the σ-algebra generated by `b` is `TauCeti.conditionalPartitionEntropy μ a b`. -/
theorem ofReal_condExpPartitionEntropy_comap_eq_conditionalPartitionEntropy [Fintype ι]
    [Countable κ] [mκ : MeasurableSpace κ] [MeasurableSingletonClass κ] {b : X → κ}
    (hb : Measurable b) {a : X → ι} (ha : ∀ i, NullMeasurableSet (a ⁻¹' {i}) μ) :
    ENNReal.ofReal (condExpPartitionEntropy μ (mκ.comap b) a) =
      conditionalPartitionEntropy μ a b :=
  (condExpCountablePartitionEntropy_eq_ofReal _ a).symm.trans
    (condExpCountablePartitionEntropy_comap_eq_conditionalPartitionEntropy hb ha)

/-- The real form of
`TauCeti.ofReal_condExpPartitionEntropy_comap_eq_conditionalPartitionEntropy`. -/
theorem condExpPartitionEntropy_comap_eq_toReal_conditionalPartitionEntropy [Fintype ι]
    [Countable κ] [mκ : MeasurableSpace κ] [MeasurableSingletonClass κ] {b : X → κ}
    (hb : Measurable b) {a : X → ι} (ha : ∀ i, NullMeasurableSet (a ⁻¹' {i}) μ) :
    condExpPartitionEntropy μ (mκ.comap b) a = (conditionalPartitionEntropy μ a b).toReal := by
  rw [← ofReal_condExpPartitionEntropy_comap_eq_conditionalPartitionEntropy hb ha,
    ENNReal.toReal_ofReal (condExpPartitionEntropy_nonneg _ a)]

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

end Probability

end TauCeti
