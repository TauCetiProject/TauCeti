/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import TauCeti.Probability.LargeDeviations.Basic

/-!
# The contraction principle

If a family `μ i` satisfies a large deviation principle with a good rate function `I` and
`f` is continuous, then the pushforwards `(μ i).map f` satisfy a large deviation principle with
the good rate function `J y = inf {I x | f x = y}`
(Dembo–Zeitouni, Theorem 4.2.1).

## Main results

* `TauCeti.Probability.HasLDP.map`: the contraction principle.
* `TauCeti.Probability.IsGoodRateFunction.contraction`: `J` is a good rate function.
-/

@[expose] public section

open Filter Topology MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι X Y : Type*}

/-- The rate function of the contraction principle: the least cost of a preimage. -/
noncomputable def contraction (f : X → Y) (I : X → ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  ⨅ x ∈ f ⁻¹' {y}, I x

theorem contraction_le {f : X → Y} {I : X → ℝ≥0∞} {x : X} : contraction f I (f x) ≤ I x :=
  iInf₂_le (f := fun x' (_ : x' ∈ f ⁻¹' {f x}) => I x') x rfl

theorem iInf_contraction (f : X → Y) (I : X → ℝ≥0∞) (A : Set Y) :
    ⨅ y ∈ A, contraction f I y = ⨅ x ∈ f ⁻¹' A, I x := by
  refine le_antisymm (le_iInf₂ fun x hx => ?_) (le_iInf₂ fun y hy => le_iInf₂ fun x hx => ?_)
  · exact iInf₂_le_of_le (f x) hx contraction_le
  · exact iInf₂_le_of_le x (by rw [mem_preimage, mem_singleton_iff.mp hx]; exact hy) le_rfl

variable [TopologicalSpace X] [TopologicalSpace Y]
namespace IsGoodRateFunction

variable [T2Space Y] {f : X → Y} {I : X → ℝ≥0∞}

/-- A good rate function attains its infimum on every fibre where the infimum is finite. -/
theorem exists_eq_contraction (hI : IsGoodRateFunction I) (hf : Continuous f) {y : Y}
    (hy : contraction f I y ≠ ∞) : ∃ x, f x = y ∧ I x = contraction f I y := by
  obtain ⟨x₁, hx₁, hlt⟩ : ∃ x₁ ∈ f ⁻¹' {y}, I x₁ < ∞ := by
    simpa only [contraction, iInf_lt_iff, exists_prop] using lt_top_iff_ne_top.mpr hy
  have hK : IsCompact ({x | I x ≤ I x₁} ∩ f ⁻¹' {y}) :=
    (hI.isCompact_sublevel _ hlt.ne).inter_right (isClosed_singleton.preimage hf)
  have hne : ({x | I x ≤ I x₁} ∩ f ⁻¹' {y}).Nonempty :=
    ⟨x₁, show I x₁ ≤ I x₁ from le_rfl, hx₁⟩
  obtain ⟨x₀, ⟨hx₀I, hx₀f⟩, hmin⟩ := (hI.lowerSemicontinuous.lowerSemicontinuousOn
    ({x | I x ≤ I x₁} ∩ f ⁻¹' {y})).exists_isMinOn hne hK
  refine ⟨x₀, hx₀f, le_antisymm (le_iInf₂ fun x hx => ?_)
    (iInf₂_le (f := fun x' (_ : x' ∈ f ⁻¹' {y}) => I x') x₀ hx₀f)⟩
  by_cases h : I x ≤ I x₁
  · exact hmin ⟨h, hx⟩
  · exact hx₀I.trans (not_le.mp h).le

/-- The contraction of a good rate function by a continuous map is a good rate function. -/
protected theorem contraction (hI : IsGoodRateFunction I) (hf : Continuous f) :
    IsGoodRateFunction (contraction f I) := by
  have hsub : ∀ α : ℝ≥0∞, α ≠ ∞ →
      {y | contraction f I y ≤ α} = f '' {x | I x ≤ α} := by
    intro α hα
    refine Set.ext fun y => ⟨fun hy => ?_, ?_⟩
    · obtain ⟨x, rfl, hx⟩ := hI.exists_eq_contraction hf (ne_top_of_le_ne_top hα hy)
      exact ⟨x, hx.le.trans hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact contraction_le.trans hx
  have hcomp : ∀ α : ℝ≥0∞, α ≠ ∞ → IsCompact {y | contraction f I y ≤ α} := fun α hα => by
    rw [hsub α hα]
    exact (hI.isCompact_sublevel α hα).image hf
  refine ⟨lowerSemicontinuous_iff_isClosed_preimage.mpr fun α => ?_, hcomp⟩
  by_cases hα : α = ∞
  · simp [hα]
  · exact (hcomp α hα).isClosed

end IsGoodRateFunction

variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] [T2Space Y]
  {l : Filter ι} {ε : ι → ℝ≥0} {μ : ι → Measure X} {I : X → ℝ≥0∞} {f : X → Y}

/-- **The contraction principle.** If `μ i` satisfies a large deviation principle with the good
rate function `I` and `f` is continuous, then `(μ i).map f` satisfies one with the good rate
function `y ↦ inf {I x | f x = y}`. -/
theorem HasLDP.map (h : HasLDP l ε μ I) (hI : IsGoodRateFunction I) (hf : Continuous f) :
    HasLDP l ε (fun i => (μ i).map f) (contraction f I) := by
  refine ⟨(hI.contraction hf).lowerSemicontinuous, fun G hG => ?_, fun F hF => ?_⟩
  · simp only [Measure.map_apply hf.measurable hG.measurableSet, iInf_contraction]
    exact h.lower_bound _ (hG.preimage hf)
  · simp only [Measure.map_apply hf.measurable hF.measurableSet, iInf_contraction]
    exact h.upper_bound _ (hF.preimage hf)

end TauCeti.Probability
