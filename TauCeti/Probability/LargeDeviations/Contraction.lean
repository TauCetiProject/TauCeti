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
* `TauCeti.Probability.IsGoodRateFunction.contractedRate`: `J` is a good rate function.
-/

public section

open Filter Topology MeasureTheory Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι X Y : Type*}

/-- The contracted rate function: the least cost of a preimage. -/
noncomputable def contractedRate (f : X → Y) (I : X → ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  ⨅ x ∈ f ⁻¹' {y}, I x

theorem contractedRate_apply (f : X → Y) (I : X → ℝ≥0∞) (y : Y) :
    contractedRate f I y = ⨅ x ∈ f ⁻¹' {y}, I x := (rfl)

theorem le_contractedRate_iff {a : ℝ≥0∞} {f : X → Y} {I : X → ℝ≥0∞} {y : Y} :
    a ≤ contractedRate f I y ↔ ∀ x, f x = y → a ≤ I x := by
  simp only [contractedRate, le_iInf₂_iff, mem_preimage, mem_singleton_iff]

theorem contractedRate_le {f : X → Y} {I : X → ℝ≥0∞} {x : X} :
    contractedRate f I (f x) ≤ I x :=
  biInf_le _ (mem_preimage.2 rfl)

@[simp]
theorem iInf_contractedRate (f : X → Y) (I : X → ℝ≥0∞) (A : Set Y) :
    ⨅ y ∈ A, contractedRate f I y = ⨅ x ∈ f ⁻¹' A, I x := by
  refine le_antisymm (le_iInf₂ fun x hx => ?_) (le_iInf₂ fun y hy => le_iInf₂ fun x hx => ?_)
  · exact iInf₂_le_of_le (f x) hx contractedRate_le
  · exact iInf₂_le_of_le x (by rw [mem_preimage, mem_singleton_iff.mp hx]; exact hy) le_rfl

variable [TopologicalSpace X] [TopologicalSpace Y]
namespace IsGoodRateFunction

variable [T1Space Y] {f : X → Y} {I : X → ℝ≥0∞}

/-- A good rate function attains its infimum on every fibre where the infimum is finite. -/
theorem exists_eq_contractedRate (hI : IsGoodRateFunction I) (hf : Continuous f) {y : Y}
    (hy : contractedRate f I y ≠ ∞) : ∃ x, f x = y ∧ I x = contractedRate f I y := by
  obtain ⟨x₁, hx₁, hlt⟩ : ∃ x₁ ∈ f ⁻¹' {y}, I x₁ < ∞ := by
    simpa only [contractedRate, iInf_lt_iff, exists_prop] using lt_top_iff_ne_top.mpr hy
  have hK : IsCompact ({x | I x ≤ I x₁} ∩ f ⁻¹' {y}) :=
    (hI.isCompact_sublevel _ hlt.ne).inter_right (isClosed_singleton.preimage hf)
  have hne : ({x | I x ≤ I x₁} ∩ f ⁻¹' {y}).Nonempty :=
    ⟨x₁, by simp, hx₁⟩
  obtain ⟨x₀, ⟨hx₀I, hx₀f⟩, hmin⟩ := (hI.lowerSemicontinuous.lowerSemicontinuousOn
    ({x | I x ≤ I x₁} ∩ f ⁻¹' {y})).exists_isMinOn hne hK
  refine ⟨x₀, hx₀f, le_antisymm (le_iInf₂ fun x hx => ?_) (biInf_le _ hx₀f)⟩
  by_cases h : I x ≤ I x₁
  · exact hmin ⟨h, hx⟩
  · exact hx₀I.trans (not_le.mp h).le

/-- A finite sublevel set of the contracted rate is the image of the corresponding sublevel set
of the original rate. -/
theorem contractedRate_sublevel (hI : IsGoodRateFunction I) (hf : Continuous f)
    (α : ℝ≥0∞) (hα : α ≠ ∞) :
    {y | contractedRate f I y ≤ α} = f '' {x | I x ≤ α} := by
  refine Set.ext fun y => ⟨fun hy => ?_, ?_⟩
  · obtain ⟨x, rfl, hx⟩ := hI.exists_eq_contractedRate hf (ne_top_of_le_ne_top hα hy)
    exact ⟨x, hx.le.trans hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact contractedRate_le.trans hx

/-- Membership in a finite sublevel set of the contracted rate is equivalent to the existence of
a preimage in the corresponding sublevel set. -/
theorem mem_contractedRate_sublevel_iff (hI : IsGoodRateFunction I) (hf : Continuous f)
    {α : ℝ≥0∞} (hα : α ≠ ∞) {y : Y} :
    contractedRate f I y ≤ α ↔ ∃ x, f x = y ∧ I x ≤ α := by
  constructor
  · intro hy
    have hmem : y ∈ {z | contractedRate f I z ≤ α} := hy
    rw [hI.contractedRate_sublevel hf α hα] at hmem
    rcases hmem with ⟨x, hx, hxy⟩
    exact ⟨x, hxy, hx⟩
  · rintro ⟨x, hxy, hx⟩
    have hmem : y ∈ f '' {x | I x ≤ α} := ⟨x, hx, hxy⟩
    rw [← hI.contractedRate_sublevel hf α hα] at hmem
    exact hmem

/-- The contraction of a good rate function by a continuous map is a good rate function. -/
protected theorem contractedRate [T2Space Y] (hI : IsGoodRateFunction I) (hf : Continuous f) :
    IsGoodRateFunction (contractedRate f I) := by
  have hcomp : ∀ α : ℝ≥0∞, α ≠ ∞ →
      IsCompact {y | contractedRate f I y ≤ α} := fun α hα => by
    rw [hI.contractedRate_sublevel hf α hα]
    exact (hI.isCompact_sublevel α hα).image hf
  refine ⟨lowerSemicontinuous_iff_isClosed_preimage.mpr fun α => ?_, hcomp⟩
  by_cases hα : α = ∞
  · simp [hα]
  · exact (hcomp α hα).isClosed

end IsGoodRateFunction

variable [MeasurableSpace X] [MeasurableSpace Y] [OpensMeasurableSpace X] [BorelSpace Y] [T2Space Y]
  {l : Filter ι} {ε : ι → ℝ≥0} {μ : ι → Measure X} {I : X → ℝ≥0∞} {f : X → Y}

/-- **The contraction principle.** If `μ i` satisfies a large deviation principle with the good
rate function `I` and `f` is continuous, then `(μ i).map f` satisfies one with the good rate
function `y ↦ inf {I x | f x = y}`. -/
theorem HasLDP.map (h : HasLDP l ε μ I) (hI : IsGoodRateFunction I) (hf : Continuous f) :
    HasLDP l ε (fun i => (μ i).map f) (contractedRate f I) := by
  refine ⟨(hI.contractedRate hf).lowerSemicontinuous, fun G hG => ?_, fun F hF => ?_⟩
  · simp only [Measure.map_apply hf.measurable hG.measurableSet, iInf_contractedRate]
    exact h.lower_bound _ (hG.preimage hf)
  · simp only [Measure.map_apply hf.measurable hF.measurableSet, iInf_contractedRate]
    exact h.upper_bound _ (hF.preimage hf)

end TauCeti.Probability
