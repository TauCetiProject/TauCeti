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
  `0 ≤ H(P | m)`, and for a probability measure
  `H(P | m) ≤ H(P) = ∑ i, negMulLog (μ.real (a ⁻¹' {i}))`.
* `TauCeti.condExpPartitionEntropy_anti`: enlarging the σ-algebra decreases the conditional
  entropy, by the conditional Jensen inequality.
* `TauCeti.condExpPartitionEntropy_bot`: conditioning on the trivial σ-algebra gives `H(P)`.
* `TauCeti.condExpPartitionEntropy_eq_zero_of_measurableSet`: conditioning on a σ-algebra for
  which the atoms are measurable, in particular on the ambient σ-algebra, gives zero.
* `TauCeti.setIntegral_condAtomProb` and `TauCeti.sum_condAtomProb_ae_eq_one`: the conditional
  probabilities integrate to the masses of the atoms over `m`-measurable sets and sum to `1`.

## References

* O. Sarig, *Lecture Notes on Ergodic Theory* (author notes dated 3 April 2023), Definition 4.2,
  with natural logarithms.
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

/-- The conditional probability of an atom is strongly measurable for the conditioning
σ-algebra. -/
theorem stronglyMeasurable_condAtomProb (a : X → ι) (i : ι) :
    StronglyMeasurable[m] (condAtomProb μ m a i) :=
  stronglyMeasurable_condExp

/-- The conditional probability of an atom is integrable. -/
theorem integrable_condAtomProb (a : X → ι) (i : ι) : Integrable (condAtomProb μ m a i) μ :=
  integrable_condExp

/-- **Degenerate cases.** The conditional probability of an atom is `0` unless `m` is a
sub-σ-algebra on which `μ` is σ-finite and the indicator of the atom is integrable. -/
theorem condAtomProb_eq_zero_or (a : X → ι) (i : ι) :
    condAtomProb μ m a i = 0 ∨ ∃ hm : m ≤ mX, SigmaFinite (μ.trim hm) ∧
      Integrable ((a ⁻¹' {i}).indicator (1 : X → ℝ)) μ := by
  by_cases hm : m ≤ mX
  swap
  · exact .inl (condExp_of_not_le hm)
  by_cases hσ : SigmaFinite (μ.trim hm)
  swap
  · exact .inl (condExp_of_not_sigmaFinite hm hσ)
  by_cases hi : Integrable ((a ⁻¹' {i}).indicator (1 : X → ℝ)) μ
  · exact .inr ⟨hm, hσ, hi⟩
  · exact .inl (condExp_of_not_integrable hi)

/-- Given a sub-σ-algebra `m`, the conditional probability of an `m`-measurable atom with
integrable indicator is its indicator. -/
theorem condAtomProb_of_measurableSet (hm : m ≤ mX) [SigmaFinite (μ.trim hm)] {a : X → ι}
    {i : ι} (hi : Integrable ((a ⁻¹' {i}).indicator (1 : X → ℝ)) μ)
    (hs : MeasurableSet[m] (a ⁻¹' {i})) :
    condAtomProb μ m a i = (a ⁻¹' {i}).indicator 1 :=
  condExp_of_stronglyMeasurable hm (stronglyMeasurable_one.indicator hs) hi

/-- The conditional probability of an `m`-measurable atom is its indicator, or `0` in the
degenerate cases. -/
theorem condAtomProb_eq_indicator_or_zero_of_measurableSet {a : X → ι} {i : ι}
    (hs : MeasurableSet[m] (a ⁻¹' {i})) :
    condAtomProb μ m a i = (a ⁻¹' {i}).indicator 1 ∨ condAtomProb μ m a i = 0 := by
  rcases condAtomProb_eq_zero_or (μ := μ) a i with h | ⟨hm, hσ, hi⟩
  · exact .inr h
  · exact .inl (condAtomProb_of_measurableSet hm hi hs)

/-- The conditional probabilities of the atoms lie in `[0, 1]` almost everywhere. No hypothesis is
needed: in the degenerate cases the conditional expectation is `0`. -/
theorem condAtomProb_mem_Icc (a : X → ι) (i : ι) :
    ∀ᵐ x ∂μ, condAtomProb μ m a i x ∈ Icc (0 : ℝ) 1 := by
  rcases condAtomProb_eq_zero_or (μ := μ) (m := m) a i with h | ⟨hm, hσ, hi⟩
  · simp [h]
  refine (convex_Icc (0 : ℝ) 1).condExp_mem hm hi isClosed_Icc
    (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ a ⁻¹' {i} <;> simp [hx]

/-- The integral of `negMulLog` of the conditional probability of an atom is nonnegative. -/
theorem integral_negMulLog_condAtomProb_nonneg (m : MeasurableSpace X) (a : X → ι) (i : ι) :
    0 ≤ ∫ x, negMulLog (condAtomProb μ m a i x) ∂μ :=
  integral_nonneg_of_ae <| (condAtomProb_mem_Icc a i).mono fun _ hx ↦ negMulLog_nonneg hx.1 hx.2

/-- The integral of the conditional probability of a null-measurable atom, given a sub-σ-algebra,
is the mass of the atom. -/
theorem integral_condAtomProb (hm : m ≤ mX) [SigmaFinite (μ.trim hm)] {a : X → ι} {i : ι}
    (hs : NullMeasurableSet (a ⁻¹' {i}) μ) :
    ∫ x, condAtomProb μ m a i x ∂μ = μ.real (a ⁻¹' {i}) := by
  rw [condAtomProb_def, integral_condExp hm, integral_indicator₀ hs]
  simp

/-- Over an `m`-measurable set `s`, the integral of the conditional probability of an atom with
integrable indicator is the mass of the part of the atom in `s`. -/
theorem setIntegral_condAtomProb (hm : m ≤ mX) [SigmaFinite (μ.trim hm)] {a : X → ι} {i : ι}
    (hi : Integrable ((a ⁻¹' {i}).indicator (1 : X → ℝ)) μ) {s : Set X}
    (hs : MeasurableSet[m] s) :
    ∫ x in s, condAtomProb μ m a i x ∂μ = μ.real (s ∩ a ⁻¹' {i}) := by
  have ha : NullMeasurableSet (a ⁻¹' {i}) (μ.restrict s) :=
    (aemeasurable_indicator_const_iff (1 : ℝ)).mp hi.restrict.aestronglyMeasurable.aemeasurable
  rw [condAtomProb_def, setIntegral_condExp hm hi hs, integral_indicator₀ ha]
  simp [measureReal_restrict_apply₀ ha, inter_comm]

/-- For a probability measure, the conditional probability of a null-measurable atom given the
trivial σ-algebra `⊥` is the constant mass of the atom. -/
theorem condAtomProb_bot [IsProbabilityMeasure μ] {a : X → ι} {i : ι}
    (hs : NullMeasurableSet (a ⁻¹' {i}) μ) :
    condAtomProb μ ⊥ a i = fun _ ↦ μ.real (a ⁻¹' {i}) := by
  rw [condAtomProb_def, condExp_bot, integral_indicator₀ hs]
  simp

variable [Fintype ι]

/-- The conditional entropy of the finite partition given by `a`, given the σ-algebra `m`: the
integral of `∑ i, negMulLog pᵢ` for the conditional probabilities `pᵢ` of the atoms. It is
meaningful for a sub-σ-algebra `m ≤ mX` on which `μ` is σ-finite; otherwise every conditional
probability is `0`, as for `condExp`, and the value is `0`. -/
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
  rcases condAtomProb_eq_zero_or (μ := μ) (m := m) a i with h | ⟨hm, -, -⟩
  · simp [h]
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact continuous_negMulLog.comp_aestronglyMeasurable
      ((stronglyMeasurable_condAtomProb a i).mono hm).aestronglyMeasurable
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
  rw [condExpPartitionEntropy_eq_sum, condExpPartitionEntropy_eq_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rcases condAtomProb_eq_zero_or (μ := μ) (m := m₂) a i with h | ⟨hm₂, -, -⟩
  · simpa [h] using integral_negMulLog_condAtomProb_nonneg m₁ a i
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

/-- The conditional probabilities of null-measurable atoms sum to `1` almost everywhere. -/
theorem sum_condAtomProb_ae_eq_one (hm : m ≤ mX) {a : X → ι}
    (ha : ∀ i, NullMeasurableSet (a ⁻¹' {i}) μ) :
    ∑ i, condAtomProb μ m a i =ᵐ[μ] 1 := by
  have hsum : ∑ i, (a ⁻¹' {i}).indicator (1 : X → ℝ) = 1 := by
    ext x
    rw [Finset.sum_apply, Finset.sum_eq_single (a x) (fun j _ hj ↦ ?_) (by simp)]
    · simp
    · simp [Ne.symm hj]
  refine ((condExp_finsetSum (f := fun i ↦ (a ⁻¹' {i}).indicator (1 : X → ℝ))
    (fun i _ ↦ (integrable_const 1).indicator₀ (ha i)) m).symm).trans ?_
  rw [hsum]
  exact EventuallyEq.of_eq (condExp_const hm (1 : ℝ))

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
  rcases condAtomProb_eq_zero_or (μ := μ) (m := m) a i with h | ⟨hm, hσ, hi⟩
  · simpa [h] using hR
  rw [← integral_condAtomProb hm
    ((aemeasurable_indicator_const_iff (1 : ℝ)).mp hi.aestronglyMeasurable.aemeasurable)]
  exact concaveOn_negMulLog.le_map_integral continuous_negMulLog.continuousOn isClosed_Ici
    ((condAtomProb_mem_Icc a i).mono fun x hx ↦ hx.1) integrable_condExp
    (integrable_negMulLog_condAtomProb a i)

/-- **Trivial σ-algebra.** For a probability measure and null-measurable atoms, conditioning on
`⊥` gives the entropy `∑ i, negMulLog (μ.real (a ⁻¹' {i}))` of the partition. -/
theorem condExpPartitionEntropy_bot [IsProbabilityMeasure μ] {a : X → ι}
    (ha : ∀ i, NullMeasurableSet (a ⁻¹' {i}) μ) :
    condExpPartitionEntropy μ ⊥ a = ∑ i, negMulLog (μ.real (a ⁻¹' {i})) := by
  rw [condExpPartitionEntropy_eq_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [condAtomProb_bot (ha i)]
  simp

/-- **Measurable atoms.** If the atoms are measurable for `m`, they are known given `m`, and the
conditional entropy is zero. In particular conditioning on the ambient σ-algebra, or on the
label itself, gives zero. -/
theorem condExpPartitionEntropy_eq_zero_of_measurableSet {a : X → ι}
    (ha : ∀ i, MeasurableSet[m] (a ⁻¹' {i})) :
    condExpPartitionEntropy μ m a = 0 := by
  have h0 : ∀ i x, negMulLog (condAtomProb μ m a i x) = 0 := fun i x ↦ by
    rcases condAtomProb_eq_indicator_or_zero_of_measurableSet (μ := μ) (ha i) with h | h
    · by_cases hx : x ∈ a ⁻¹' {i} <;> simp [h, hx]
    · simp [h]
  simp [condExpPartitionEntropy_def, h0]

end TauCeti
