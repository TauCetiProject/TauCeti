/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Conditional entropy of a finite partition given a sub-σ-algebra

Let `μ` be a measure on `X` and `a : X → ι` a label into a finite type, representing the finite
partition of `X` into the atoms `a ⁻¹' {i}` (empty atoms included). For a σ-algebra `m` on `X`,
the conditional probability of the atom `a ⁻¹' {i}` is the conditional expectation
`condAtomProb μ m a i = μ[(a ⁻¹' {i}).indicator 1 | m]`, and the conditional entropy of the
partition given `m` is

`condExpPartitionEntropy μ m a = ∫ x, ∑ i, negMulLog (condAtomProb μ m a i x) ∂μ`,

in natural units. The conditional probabilities lie in `[0, 1]` almost everywhere, so for a finite
measure this is the integral of a bounded function. No standard-Borel or countable-generation
hypothesis is placed on `X`.

## Main results

* `TauCeti.condExpPartitionEntropy_congr`: the value does not depend on the representatives of
  the conditional probabilities.
* `TauCeti.condExpPartitionEntropy_nonneg` and `TauCeti.condExpPartitionEntropy_le`:
  `0 ≤ H(P | m) ≤ H(P) = ∑ i, negMulLog (μ.real (a ⁻¹' {i}))`.
* `TauCeti.condExpPartitionEntropy_anti`: enlarging the σ-algebra decreases the conditional
  entropy, by the conditional Jensen inequality.
* `TauCeti.condExpPartitionEntropy_bot`: conditioning on the trivial σ-algebra gives `H(P)`.
* `TauCeti.condExpPartitionEntropy_eq_zero_of_measurable`: conditioning on a σ-algebra for which
  the label is measurable, in particular on the ambient σ-algebra, gives zero.

## References

* The definitions follow the roadmap ArithmeticDynamics, §2.7, Measure entropy and maximizing
  measures, which cites O. Sarig, Lecture Notes on Ergodic Theory (author notes dated 3 April
  2023), Definition 4.2, with natural logarithms.
-/

public section

open MeasureTheory Real Set Filter
open scoped ENNReal

namespace TauCeti

variable {X ι : Type*} {m m₁ m₂ : MeasurableSpace X} {mX : MeasurableSpace X} {μ : Measure X}

/-- The conditional probability `μ[1_{a = i} | m]` of the atom `a ⁻¹' {i}` given the σ-algebra
`m`. -/
noncomputable def condAtomProb (μ : Measure X) (m : MeasurableSpace X) (a : X → ι) (i : ι) :
    X → ℝ :=
  μ[(a ⁻¹' {i}).indicator 1 | m]

theorem condAtomProb_def (μ : Measure X) (m : MeasurableSpace X) (a : X → ι) (i : ι) :
    condAtomProb μ m a i = μ[(a ⁻¹' {i}).indicator 1 | m] :=
  (rfl)

variable [Fintype ι]

/-- The conditional entropy of the finite partition given by `a`, given the σ-algebra `m`: the
integral of `∑ i, negMulLog pᵢ` for the conditional probabilities `pᵢ` of the atoms. -/
noncomputable def condExpPartitionEntropy (μ : Measure X) (m : MeasurableSpace X) (a : X → ι) :
    ℝ :=
  ∫ x, ∑ i, negMulLog (condAtomProb μ m a i x) ∂μ

theorem condExpPartitionEntropy_def (μ : Measure X) (m : MeasurableSpace X) (a : X → ι) :
    condExpPartitionEntropy μ m a = ∫ x, ∑ i, negMulLog (condAtomProb μ m a i x) ∂μ :=
  (rfl)

/-- **Independence of representatives.** Any almost-everywhere representatives of the conditional
probabilities give the same conditional entropy. -/
theorem condExpPartitionEntropy_congr {a : X → ι} {p : ι → X → ℝ}
    (hp : ∀ i, p i =ᵐ[μ] condAtomProb μ m a i) :
    condExpPartitionEntropy μ m a = ∫ x, ∑ i, negMulLog (p i x) ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.mpr hp] with x hx
  simp [hx]

omit [Fintype ι] in
/-- The conditional probabilities of the atoms lie in `[0, 1]` almost everywhere. No hypothesis is
needed: in the degenerate cases the conditional expectation is `0`. -/
theorem condAtomProb_mem_Icc (a : X → ι) (i : ι) :
    ∀ᵐ x ∂μ, condAtomProb μ m a i x ∈ Icc (0 : ℝ) 1 := by
  by_cases hm : m ≤ mX
  swap
  · simp [condAtomProb_def, condExp_of_not_le hm]
  by_cases hσ : SigmaFinite (μ.trim hm)
  swap
  · simp [condAtomProb_def, condExp_of_not_sigmaFinite hm hσ]
  by_cases hi : Integrable ((a ⁻¹' {i}).indicator (1 : X → ℝ)) μ
  swap
  · simp [condAtomProb_def, condExp_of_not_integrable hi]
  refine (convex_Icc (0 : ℝ) 1).condExp_mem hm hi isClosed_Icc
    (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ a ⁻¹' {i} <;> simp [hx]

/-- The conditional entropy is nonnegative. -/
theorem condExpPartitionEntropy_nonneg (m : MeasurableSpace X) (a : X → ι) :
    0 ≤ condExpPartitionEntropy μ m a := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_all_iff.mpr (condAtomProb_mem_Icc (μ := μ) (m := m) a)] with x hx
  exact Finset.sum_nonneg fun i _ ↦ negMulLog_nonneg (hx i).1 (hx i).2

section Finite

variable [IsFiniteMeasure μ]

omit [Fintype ι] in
/-- For a finite measure, `negMulLog` of a conditional atom probability is integrable. -/
theorem integrable_negMulLog_condAtomProb (a : X → ι) (i : ι) :
    Integrable (fun x ↦ negMulLog (condAtomProb μ m a i x)) μ := by
  by_cases hm : m ≤ mX
  swap
  · simp [condAtomProb_def, condExp_of_not_le hm]
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact continuous_negMulLog.comp_aestronglyMeasurable
      (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
  · filter_upwards [condAtomProb_mem_Icc a i] with x hx
    rw [Real.norm_of_nonneg (negMulLog_nonneg hx.1 hx.2)]
    exact (negMulLog_le_one_sub_self hx.1).trans (by linarith [hx.1])

/-- The conditional entropy is the sum over the atoms of the integrals of `negMulLog pᵢ`. -/
theorem condExpPartitionEntropy_eq_sum (m : MeasurableSpace X) (a : X → ι) :
    condExpPartitionEntropy μ m a = ∑ i, ∫ x, negMulLog (condAtomProb μ m a i x) ∂μ :=
  integral_finsetSum _ fun i _ ↦ integrable_negMulLog_condAtomProb a i

/-- **Monotonicity.** Enlarging the σ-algebra decreases the conditional entropy:
`H(P | m₂) ≤ H(P | m₁)` for `m₁ ≤ m₂`. -/
theorem condExpPartitionEntropy_anti (h₁₂ : m₁ ≤ m₂) (a : X → ι) :
    condExpPartitionEntropy μ m₂ a ≤ condExpPartitionEntropy μ m₁ a := by
  by_cases hm₂ : m₂ ≤ mX
  swap
  · simpa [condExpPartitionEntropy_def, condAtomProb_def, condExp_of_not_le hm₂] using
      condExpPartitionEntropy_nonneg m₁ a
  rw [condExpPartitionEntropy_eq_sum, condExpPartitionEntropy_eq_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  -- Tower property and conditional Jensen for the concave `negMulLog` on `[0, 1]`.
  have hJ := (strictConcaveOn_negMulLog.concaveOn.subset Icc_subset_Ici_self
    (convex_Icc 0 1)).condExp_map_le (μ := μ) (h₁₂.trans hm₂)
    continuous_negMulLog.continuousOn.upperSemicontinuousOn
    (condAtomProb_mem_Icc (m := m₂) a i) isClosed_Icc integrable_condExp
    (integrable_negMulLog_condAtomProb (m := m₂) a i)
  have htower : μ[condAtomProb μ m₂ a i | m₁] =ᵐ[μ] condAtomProb μ m₁ a i :=
    condExp_condExp_of_le h₁₂ hm₂
  calc ∫ x, negMulLog (condAtomProb μ m₂ a i x) ∂μ
      = ∫ x, μ[fun x ↦ negMulLog (condAtomProb μ m₂ a i x) | m₁] x ∂μ :=
        (integral_condExp (h₁₂.trans hm₂)).symm
    _ ≤ ∫ x, negMulLog (condAtomProb μ m₁ a i x) ∂μ := by
        refine integral_mono_ae integrable_condExp
          (integrable_negMulLog_condAtomProb (m := m₁) a i) ?_
        filter_upwards [hJ, htower] with x hx hx'
        simpa [Function.comp_def, hx'] using hx

omit [Fintype ι] in
/-- The integral of the conditional probability of a null-measurable atom, given a sub-σ-algebra,
is the mass of the atom. -/
theorem integral_condAtomProb (hm : m ≤ mX) {a : X → ι} {i : ι}
    (hs : NullMeasurableSet (a ⁻¹' {i}) μ) :
    ∫ x, condAtomProb μ m a i x ∂μ = μ.real (a ⁻¹' {i}) := by
  rw [condAtomProb_def, integral_condExp hm, integral_indicator₀ hs]
  simp

end Finite

/-- **Upper bound.** For a probability measure the conditional entropy is at most the entropy
`∑ i, negMulLog (μ.real (a ⁻¹' {i}))` of the partition, by Jensen's inequality. -/
theorem condExpPartitionEntropy_le [IsProbabilityMeasure μ] (a : X → ι) :
    condExpPartitionEntropy μ m a ≤ ∑ i, negMulLog (μ.real (a ⁻¹' {i})) := by
  rw [condExpPartitionEntropy_eq_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  have hR : 0 ≤ negMulLog (μ.real (a ⁻¹' {i})) :=
    negMulLog_nonneg measureReal_nonneg measureReal_le_one
  -- In the degenerate cases the conditional probability vanishes.
  by_cases hm : m ≤ mX
  swap
  · simpa [condAtomProb_def, condExp_of_not_le hm] using hR
  by_cases hi : Integrable ((a ⁻¹' {i}).indicator (1 : X → ℝ)) μ
  swap
  · simpa [condAtomProb_def, condExp_of_not_integrable hi] using hR
  have hpre : (a ⁻¹' {i}).indicator (1 : X → ℝ) ⁻¹' {1} = a ⁻¹' {i} := by
    ext x
    by_cases hx : x ∈ a ⁻¹' {i} <;> simp [hx]
  have hs : NullMeasurableSet (a ⁻¹' {i}) μ :=
    hpre ▸ hi.aestronglyMeasurable.aemeasurable.nullMeasurable (measurableSet_singleton 1)
  rw [← integral_condAtomProb hm hs]
  exact concaveOn_negMulLog.le_map_integral continuous_negMulLog.continuousOn isClosed_Ici
    ((condAtomProb_mem_Icc a i).mono fun x hx ↦ hx.1) integrable_condExp
    (integrable_negMulLog_condAtomProb a i)

/-- **Trivial σ-algebra.** For a probability measure and a measurable label, conditioning on `⊥`
gives the entropy `∑ i, negMulLog (μ.real (a ⁻¹' {i}))` of the partition. -/
theorem condExpPartitionEntropy_bot [IsProbabilityMeasure μ] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {a : X → ι} (ha : Measurable a) :
    condExpPartitionEntropy μ ⊥ a = ∑ i, negMulLog (μ.real (a ⁻¹' {i})) := by
  rw [condExpPartitionEntropy_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [condAtomProb_def, condExp_bot,
    integral_indicator_one (ha (measurableSet_singleton i))]
  simp

/-- **Measurable label.** If the label is measurable for `m`, its atoms are known given `m`, and
the conditional entropy is zero. In particular conditioning on the ambient σ-algebra, or on the
label itself, gives zero. -/
theorem condExpPartitionEntropy_eq_zero_of_measurable [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {a : X → ι} (ha : Measurable[m] a) :
    condExpPartitionEntropy μ m a = 0 := by
  have h01 : ∀ i x, negMulLog (condAtomProb μ m a i x) = 0 := fun i x ↦ by
    have hs : MeasurableSet[m] (a ⁻¹' {i}) := ha (measurableSet_singleton i)
    have hval : condAtomProb μ m a i x = (a ⁻¹' {i}).indicator 1 x ∨
        condAtomProb μ m a i x = 0 := by
      by_cases hm : m ≤ mX
      swap
      · exact Or.inr (by rw [condAtomProb_def, condExp_of_not_le hm, Pi.zero_apply])
      by_cases hσ : SigmaFinite (μ.trim hm)
      · by_cases hi : Integrable ((a ⁻¹' {i}).indicator (1 : X → ℝ)) μ
        · left
          rw [condAtomProb_def, condExp_of_stronglyMeasurable hm
            (stronglyMeasurable_one.indicator hs) hi]
        · right
          rw [condAtomProb_def, condExp_of_not_integrable hi, Pi.zero_apply]
      · right
        rw [condAtomProb_def, condExp_of_not_sigmaFinite hm hσ, Pi.zero_apply]
    rcases hval with h | h
    · by_cases hx : x ∈ a ⁻¹' {i} <;> simp [h, hx]
    · simp [h]
  simp [condExpPartitionEntropy_def, h01]

end TauCeti
