/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Arrays.Extreme.Basic
public import TauCeti.Probability.Exchangeability.Arrays.AldousHoover.Decomposition

/-!
# Extreme separately exchangeable array laws

Independent finitely supported relabelings of the row and column indices act on array space.
Their invariant probability laws are exactly the separately exchangeable laws. For such a law,
ergodicity of this action is equivalent to joint dissociation: a corner-tail event is fixed by
both relabelings, while joint dissociation already makes the smaller diagonal action ergodic.
The general ergodic/extreme-point theorem then identifies the extreme separately exchangeable
laws with the jointly dissociated ones.

This is the ergodic component interface for the separate Aldous--Hoover representation. Its
extreme laws are the components for which the global noise can be removed. The existing
corner-tail disintegration therefore becomes a measurable mixture of extreme separately
exchangeable laws.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables",
  *Journal of Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
-/

public section

open Filter MeasureTheory ProbabilityTheory TauCeti.MeasureTheory Set
open scoped ENNReal

namespace TauCeti.Probability

variable {α : Type*} [MeasurableSpace α]

/-- The separately exchangeable probability laws on array path space. -/
def separatelyExchangeableProbabilityMeasures (α : Type*) [MeasurableSpace α] :
    Set (Measure (ℕ × ℕ → α)) :=
  {ρ | SeparatelyExchangeable ρ (fun p x ↦ x p) ∧ IsProbabilityMeasure ρ}

/-- Membership in the separately exchangeable probability laws. -/
@[simp]
theorem mem_separatelyExchangeableProbabilityMeasures_iff
    {ρ : Measure (ℕ × ℕ → α)} :
    ρ ∈ separatelyExchangeableProbabilityMeasures α ↔
      SeparatelyExchangeable ρ (fun p x ↦ x p) ∧ IsProbabilityMeasure ρ :=
  Iff.rfl

/-- Separately exchangeable probability laws are the invariant probability laws of the
independent finitary action. -/
theorem separatelyExchangeableProbabilityMeasures_eq :
    separatelyExchangeableProbabilityMeasures α =
      invariantMeasuresOfMeasureUnivEq (FinitaryPerm × FinitaryPerm) (ℕ × ℕ → α) 1 := by
  ext ρ
  rw [mem_invariantMeasuresOfMeasureUnivEq_iff]
  constructor
  · rintro ⟨hexch, hp⟩
    exact ⟨hexch.smulInvariantMeasure_pair, hp.measure_univ⟩
  · rintro ⟨hinv, hp⟩
    have : IsProbabilityMeasure ρ := ⟨hp⟩
    exact ⟨separatelyExchangeable_of_smulInvariantMeasure_pair, inferInstance⟩

/-- The separately exchangeable probability laws form a convex set. -/
theorem convex_separatelyExchangeableProbabilityMeasures :
    Convex ℝ≥0∞ (separatelyExchangeableProbabilityMeasures α) := by
  rw [separatelyExchangeableProbabilityMeasures_eq]
  exact convex_invariantMeasuresOfMeasureUnivEq

/-- A separately exchangeable probability law is extreme exactly when it is jointly
dissociated. -/
theorem jointlyDissociated_iff_mem_extremePoints_separatelyExchangeable
    {ρ : Measure (ℕ × ℕ → α)} [IsProbabilityMeasure ρ]
    (hexch : SeparatelyExchangeable ρ fun p x ↦ x p) :
    JointlyDissociated ρ (fun p x ↦ x p) ↔
      ρ ∈ extremePoints ℝ≥0∞ (separatelyExchangeableProbabilityMeasures α) := by
  rw [jointlyDissociated_iff_ergodicSMul_pair hexch,
    separatelyExchangeableProbabilityMeasures_eq]
  exact ErgodicSMul.iff_mem_extremePoints

/-- Every separately exchangeable probability law is a measurable mixture of extreme separately
exchangeable laws. The components are the jointly dissociated conditional laws of the array given
its corner tail. -/
theorem SeparatelyExchangeable.exists_extreme_kernel
    [StandardBorelSpace α] {ρ : Measure (ℕ × ℕ → α)} [IsProbabilityMeasure ρ]
    (hρ : SeparatelyExchangeable ρ fun p x ↦ x p) :
    ∃ κ : ProbabilityTheory.Kernel unitInterval (ℕ × ℕ → α), IsMarkovKernel κ ∧
      (∀ᵐ u ∂(volume : Measure unitInterval),
        κ u ∈ extremePoints ℝ≥0∞ (separatelyExchangeableProbabilityMeasures α)) ∧
      κ ∘ₘ (volume : Measure unitInterval) = ρ := by
  obtain ⟨κ, hκ, hgood, hmix⟩ := hρ.exists_jointlyDissociated_kernel
  let := hκ
  refine ⟨κ, hκ, ?_, hmix⟩
  filter_upwards [hgood] with u hu
  exact (jointlyDissociated_iff_mem_extremePoints_separatelyExchangeable hu.1).mp hu.2

end TauCeti.Probability
