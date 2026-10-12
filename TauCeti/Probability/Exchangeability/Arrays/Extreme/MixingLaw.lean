/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Representation
public import TauCeti.Probability.Exchangeability.Arrays.Extreme.Basic
public import TauCeti.Probability.Exchangeability.RandomMeasure.Basic

/-!
# Extremality of the row mixing law of a dissociated array

The row-coding representation associates to a separately exchangeable array a unique law on
probability measures on row paths, invariant under column permutations. If the array
is jointly dissociated, this mixing law is extreme among such invariant probability laws: a
nontrivial convex decomposition of it would give a convex decomposition of the array law into
jointly exchangeable laws, contradicting dissociation.

Thus, for a dissociated array, the first row-coding stage of the separate Aldous--Hoover
representation is driven by an extreme column-invariant law on row-path measures; resolving such
a law into column and cell noise gives the functional representation of the array.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]

/-- A jointly dissociated row-coding law has an extreme column-invariant mixing law. If it is a
nontrivial convex combination of two column-invariant probability laws, both laws equal it. -/
private theorem eq_of_rowCodingArrayLaw_jointlyDissociated_convexComb
    {π π₁ π₂ : Measure (ProbabilityMeasure (ℕ → α))}
    [IsProbabilityMeasure π] [IsProbabilityMeasure π₁] [IsProbabilityMeasure π₂]
    (hπ : ∀ τ : Equiv.Perm ℕ, π.map (fun P ↦ P.map (permReindex τ)) = π)
    (hπ₁ : ∀ τ : Equiv.Perm ℕ, π₁.map (fun P ↦ P.map (permReindex τ)) = π₁)
    (hπ₂ : ∀ τ : Equiv.Perm ℕ, π₂.map (fun P ↦ P.map (permReindex τ)) = π₂)
    (h : JointlyDissociated (rowCodingArrayLaw π) (fun p x ↦ x p))
    {a b : ℝ≥0∞} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hcomb : π = a • π₁ + b • π₂) : π₁ = π ∧ π₂ = π := by
  have hρ₁ : JointlyExchangeable (rowCodingArrayLaw π₁) (fun p x ↦ x p) :=
    (separatelyExchangeable_rowCodingArrayLaw π₁ hπ₁).jointlyExchangeable
  have hρ₂ : JointlyExchangeable (rowCodingArrayLaw π₂) (fun p x ↦ x p) :=
    (separatelyExchangeable_rowCodingArrayLaw π₂ hπ₂).jointlyExchangeable
  have hρ : JointlyExchangeable (rowCodingArrayLaw π) (fun p x ↦ x p) :=
    (separatelyExchangeable_rowCodingArrayLaw π hπ).jointlyExchangeable
  have hext := (jointlyDissociated_iff_mem_extremePoints hρ).mp h
  have hopen : rowCodingArrayLaw π ∈
      openSegment ℝ≥0∞ (rowCodingArrayLaw π₁) (rowCodingArrayLaw π₂) := by
    exact ⟨a, b, ha, hb, hab, by
      rw [← rowCodingArrayLaw_smul, ← rowCodingArrayLaw_smul,
        ← rowCodingArrayLaw_add, ← hcomb]⟩
  have hm₁ : rowCodingArrayLaw π₁ ∈ jointlyExchangeableProbabilityMeasures α :=
    mem_jointlyExchangeableProbabilityMeasures_iff.mpr ⟨hρ₁, inferInstance⟩
  have hm₂ : rowCodingArrayLaw π₂ ∈ jointlyExchangeableProbabilityMeasures α :=
    mem_jointlyExchangeableProbabilityMeasures_iff.mpr ⟨hρ₂, inferInstance⟩
  have hboth := (mem_extremePoints.mp hext).2 _ hm₁ _ hm₂ hopen
  exact ⟨eq_of_rowCodingArrayLaw_eq hboth.1, eq_of_rowCodingArrayLaw_eq hboth.2⟩

/-- The mixing law of a jointly dissociated row-coding array is an extreme invariant law. -/
theorem mem_extremePoints_columnInvariantMixingProbabilityMeasures_of_jointlyDissociated
    {π : Measure (ProbabilityMeasure (ℕ → α))} [IsProbabilityMeasure π]
    (hπ : ∀ τ : Equiv.Perm ℕ, π.map (fun P ↦ P.map (permReindex τ)) = π)
    (h : JointlyDissociated (rowCodingArrayLaw π) (fun p x ↦ x p)) :
    π ∈ Set.extremePoints ℝ≥0∞ (columnInvariantMixingProbabilityMeasures α) := by
  refine (mem_extremePoints_iff_left).2
    ⟨mem_columnInvariantMixingProbabilityMeasures_iff.mpr ⟨inferInstance, hπ⟩, ?_⟩
  intro π₁ hπ₁ π₂ hπ₂ hseg
  obtain ⟨hp₁, hi₁⟩ := mem_columnInvariantMixingProbabilityMeasures_iff.mp hπ₁
  obtain ⟨hp₂, hi₂⟩ := mem_columnInvariantMixingProbabilityMeasures_iff.mp hπ₂
  have : IsProbabilityMeasure π₁ := hp₁
  have : IsProbabilityMeasure π₂ := hp₂
  obtain ⟨a, b, ha, hb, hab, hcomb⟩ := hseg
  exact (eq_of_rowCodingArrayLaw_jointlyDissociated_convexComb hπ hi₁ hi₂ h
    ha hb hab hcomb.symm).1

/-- A separately exchangeable, jointly dissociated array has a row mixing law which is extreme
among column-invariant probability laws on row-path measures. -/
theorem SeparatelyExchangeable.exists_rowCodingArrayLaw_eq_mem_extremePoints
    {ρ : Measure (ℕ × ℕ → α)} [IsProbabilityMeasure ρ]
    (hexch : SeparatelyExchangeable ρ (fun p x ↦ x p))
    (hdiss : JointlyDissociated ρ (fun p x ↦ x p)) :
    ∃ π : ProbabilityMeasure (ProbabilityMeasure (ℕ → α)),
      ρ = rowCodingArrayLaw π ∧
        (π : Measure (ProbabilityMeasure (ℕ → α))) ∈
          Set.extremePoints ℝ≥0∞ (columnInvariantMixingProbabilityMeasures α) := by
  obtain ⟨π, hπ, hlaw⟩ :=
    (separatelyExchangeable_iff_exists_rowCodingArrayLaw
      (μ := ρ) (X := fun p x ↦ x p) (fun p ↦ (measurable_pi_apply p).aemeasurable)).mp hexch
  have hlaw' : ρ = rowCodingArrayLaw π := by
    simpa only [Measure.map_id'] using hlaw
  refine ⟨π, hlaw', ?_⟩
  exact mem_extremePoints_columnInvariantMixingProbabilityMeasures_of_jointlyDissociated hπ
    (hlaw' ▸ hdiss)

end TauCeti.Probability
